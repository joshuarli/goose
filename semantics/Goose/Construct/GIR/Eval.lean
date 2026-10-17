import Goose.Construct.GIR.Syntax
import Goose.Construct.Runtime
import Std.Data.HashMap

namespace Goose.Construct.GIR
open Goose.Core (ActId ScopeInst RootInst Loc OriginId DestinationId StorageId NumProfile AbortKind IntTy)

inductive RVal
  | value (value : Value)
  | copied (value : Value) (source : Core.CopySource)
  | rendered (bytes : ByteArray)
  | view (view : RuntimeView) (source : Option Core.CopySource := none)
  | dest (id : DestinationId)
  | ownerExtension (id : DestinationId) (snapshot : PendingDestination)
  | built (id : DestinationId)
  | cancelled (id : DestinationId)
  | directCancelled (id : DestinationId)
  | receiving (id : DestinationId) (owner : ActId)
  | waitingReservation (token : ExitReservationId) (incoming : DestinationId) (owner : ActId)
      (receiver : ValueId)
  | exitReservation (token : Option ExitReservationId) (selected incoming : DestinationId)
      (receiver : ValueId)
      (kind : ExitTicketKind) (org : Option OriginId)
  | pack (carriers : List Carrier)

structure Config where
  module : Module
  profile : NumProfile

def Config.layout (config : Config) : LayoutEnv := ⟨config.module.structs⟩

structure Frame where
  function : FnId
  activation : RuntimeActivation
  vals : Std.HashMap ValueId RVal := {}
  named : List (SlotId × DestinationId) := []
  parameterOrdinals : List StorageId := []
  copySources : Std.HashMap ValueId Core.CopySource := {}
  pushOwners : List (Loc × Loc) := []
  ownerExtensionSnapshots : List (DestinationId × PendingDestination) := []
  waitingCancelWitnesses : List (ValueId × ValueId × ExitReservationId × List DestinationId) := []
  waitingTickets : List (ValueId × ExitReservationId) := []
  waitingReceipts : List (ValueId × Goose.Construct.BorrowedWaitingExitReservation) := []
  releasedWaitingTickets : List ValueId := []
  terminalWaitingRelease : Bool := false
  landedExitTickets : List ValueId := []
  releasedAdoptedTickets : List ValueId := []

inductive ExecOutcome
  | returned (carriers : List Carrier)
  | escaped (address : ExitAddress) (carriers : List Carrier) (cancellations : List RVal)

private def getCell (frame : Frame) (id : ValueId) : EvalM RVal :=
  match frame.vals[id]? with
  | some (.value value) => match frame.copySources[id]? with
    | some source => pure (.copied value source)
    | none => pure (.value value)
  | some value => pure value
  | none => fault .unbound

private def getValue (frame : Frame) (id : ValueId) : EvalM Value := do
  match ← getCell frame id with | .value value | .copied value _ => pure value | _ => fault .shape

private def getView (frame : Frame) (id : ValueId) : EvalM RuntimeView := do
  match ← getCell frame id with | .view view _ => pure view | _ => fault .shape

private def getDest (frame : Frame) (id : ValueId) : EvalM DestinationId := do
  match ← getCell frame id with | .dest id => pure id | _ => fault .shape

private def getBuilt (frame : Frame) (id : ValueId) : EvalM DestinationId := do
  match ← getCell frame id with | .built id => pure id | _ => fault .shape

private def getReceiving (frame : Frame) (id : ValueId) : EvalM (DestinationId × ActId) := do
  match ← getCell frame id with | .receiving destination owner => pure (destination,owner) | _ => fault .shape

private def restoreCompletedChildOwner (frame : Frame) (incoming : DestinationId)
    (carried : List DestinationId) : EvalM Unit := do
  match frame.ownerExtensionSnapshots.find? (·.1 == incoming) with
  | some (_,snapshot) => restoreCompletedOwner snapshot incoming carried
  | none => pure ()

private def getExitReservation (frame : Frame) (id : ValueId) :
    EvalM (Option ExitReservationId × DestinationId × DestinationId × ValueId × ExitTicketKind × Option OriginId) := do
  match ← getCell frame id with
  | .exitReservation token selected incoming receiver source org => pure (token,selected,incoming,receiver,source,org)
  | _ => fault .shape

private def getWaitingExitReservation (frame : Frame) (id : ValueId) :
    EvalM (ExitReservationId × DestinationId × ActId × ValueId) := do
  match ← getCell frame id with
  | .waitingReservation token incoming owner receiver => pure (token,incoming,owner,receiver)
  | _ => fault .shape

private def getProtocol (frame : Frame) (id : ValueId) : EvalM DestinationId := do
  match ← getCell frame id with
  | .dest id | .built id | .cancelled id => pure id
  | _ => fault .shape

private def getCarrier (frame : Frame) (id : ValueId) : EvalM Carrier := do
  match ← getCell frame id with
  | .value value | .copied value _ => pure (.register value)
  | .built id => pure (.completed id)
  | _ => fault .shape

private def packResults (carriers : List Carrier) : RVal :=
  match carriers with
  | [] => .value .unit
  | [.register value] => .value value
  | [.completed id] => .built id
  | values => .pack values

private def bindParams (frame : Frame) (params : List (ValueId × VTy)) (values : List RVal) : EvalM Frame := do
  unless params.length == values.length do fault .arity
  let sources := (params.zip values).foldl (fun sources ((id,_),value) => match value with
    | .copied _ source => sources.insert id source
    | _ => sources.erase id) frame.copySources
  pure { frame with vals := (params.zip values).foldl (fun map ((id,_),value) => map.insert id value) frame.vals, copySources := sources }

private def origin (org : Option OriginId) : EvalM OriginId :=
  match org with | some org => pure org | none => fault .unbound

private def liftProtocol (action : ConstructionM α) : EvalM α := fun state =>
  match action state.construction with
  | .ok value construction => .ok value { state with construction }
  | .fault _ construction => .stop (.fault .flow) { state with construction }

private def releaseReservationsForStop (first : Nat) : EvalM Unit := do
  let size := (← EvalM.get).construction.exitReservations.size
  unless first ≤ size do fault .flow
  for offset in (List.range (size - first)).reverse do
    let token := first + offset
    let state ← EvalM.get
    match state.construction.exitReservations[token]? with
    | some .released => pure ()
    | some (.waiting _) | some (.active ..) | some .restored =>
        liftProtocol (releaseExitReservation token)
    | _ => fault .flow

private def numeric (org : Option OriginId) (action : Except Core.NumAbort Int) : EvalM Int :=
  match action with
  | .ok value => pure value
  | .error kind => do abortAt (match kind with | .divZero => .divZero | .divOverflow => .divOverflow | .intOverflow => .intOverflow | .castRange => .castRange) (← origin org)

private def slotLoc (function : Func) (frame : Frame) (id : SlotId) : EvalM Loc := do
  let some slot := function.slots[id]? | fault .unbound
  let some (_,scope) := frame.activation.scopes.find? (fun s => s.1 == slot.scope) | fault .unbound
  pure ⟨.local frame.activation.act scope id, []⟩

private def setActivation (activation : RuntimeActivation) : EvalM Unit := do
  let state ← EvalM.get
  EvalM.set { state with activations := state.activations.map fun current => if current.act == activation.act then activation else current }

private def sample (fuel : Nat) (config : Config) (location : Loc) : EvalM RuntimeView := do
  let (count,dynamic) ← arrayLength (← readLoc fuel config.layout location)
  pure ⟨location,0,count,dynamic⟩

private def indexLocation (view : RuntimeView) (index : Int) (checked : Bool) (org : Option OriginId) : EvalM Loc := do
  if index < 0 || index.toNat >= view.count then
    if checked then abortAt .indexOob (← origin org) else fault .pathRange
  pure ⟨view.location.root, view.location.path ++ [view.start + index.toNat]⟩

private def arrayBound (frame : Frame) (length : Nat) (default : Int) : Bnd → EvalM Int
  | .omitted => pure default
  | .val id => do pure (← expectInt (← getValue frame id)).2
  | .fromEnd id => do pure (Int.ofNat length - (← expectInt (← getValue frame id)).2)

private def writeBytes (destination : DestinationId) (bytes : ByteArray) (org : OriginId) : EvalM Unit :=
  bytes.data.toList.forM fun byte => liftConstruction org (writeElement destination ⟨#[byte]⟩)

private def renderCell (fuel : Nat) (config : Config) (cell : RVal) : EvalM ByteArray := do
  match cell with
  | .value value | .copied value _ => renderAny fuel config.layout .topLevel value
  | .view view _ => renderView fuel config.layout .topLevel view
  | .rendered bytes => pure bytes
  | _ => fault .shape

private def sourceOfLocation (location : Loc) : EvalM Core.CopySource := do
  let some object := (← EvalM.get).objectOrdinals.lookup location.root | fault .unbound
  pure (.storage object location.path)

private def openReceiver (fuel : Nat) (config : Config) (function : Func) (frame : Frame)
    (receiver : DestReceiver) (logical : Ty) (request : Core.ConstructionRequest) (count : Option Nat) (org : OriginId) : EvalM (DestinationId × Option PendingDestination) := do
  let snapshot (stored : StoredValue) : EvalM (Option PendingDestination) := do
    match stored.destination with
    | none => pure none
    | some id => do
        let parent ← getDestination id
        pure (if parent.progress matches .built _ then some parent else none)
  let fresh (location : Loc) (receiving : Ty) : EvalM DestinationId := do
    let storage ← reserveRootObject location.root
    let capability : Core.Destination Ty := ⟨0,location,receiving,logical,request,0,frame.activation.act⟩
    liftConstruction org (openDestinationDirect storage capability (← receivingLayout config.layout receiving) count)
  match receiver with
  | .slot slot => do
      let some descriptor := function.slots[slot]? | fault .unbound
      pure (← fresh (← slotLoc function frame slot) descriptor.ty, none)
  | .global global => do
      let some descriptor := config.module.globals[global]? | fault .unbound
      pure (← fresh ⟨.global global,[]⟩ descriptor.ty, none)
  | .arg _ position => do
      let scope ← freshScope
      pure (← fresh ⟨.local frame.activation.act scope (function.slots.size + position),[]⟩ logical, none)
  | .append reference | .whole reference => do
      let location ← expectRef (← getValue frame reference)
      if receiver matches .whole _ then truncateOwner fuel config.layout location 0 org
      let .stored stored ← readLoc fuel config.layout location | fault .shape
      let ownerSnapshot ← snapshot stored
      let id ← ownerDestination config.layout stored request count org
      let state ← EvalM.get
      let some pending := state.construction.destinations[id]? | fault .unbound
      let pending := { pending with capability := { pending.capability with receiver := location, logicalType := logical } }
      EvalM.set { state with construction := { state.construction with destinations := state.construction.destinations.set! id pending } }
      pure (id,ownerSnapshot)
  | .push reference => do
      let location ← expectRef (← getValue frame reference)
      let .stored stored ← readLoc fuel config.layout location | fault .shape
      let ownerSnapshot ← snapshot stored
      let id ← openElementReceiving config.layout frame.activation.act location stored logical count org
      pure (id,ownerSnapshot)

private def publishDestination (fuel : Nat) (config : Config) (id : DestinationId) (org : OriginId)
    (elementReceiver : Option Loc := none) : EvalM Unit := do
  if let some location := elementReceiver then
    let .stored stored ← readLoc fuel config.layout location | fault .shape
    publishElementReceiving fuel config.layout location stored id org
    return
  let pending ← getDestination id
  let location := pending.capability.receiver
  match pending.use with
  | .child _ =>
      let .stored stored ← readLoc fuel config.layout location | fault .shape
      publishOwner fuel config.layout location stored id org
  | .receiver =>
      match (← EvalM.get).objects.lookup location.root with
      | some _ =>
          let .stored stored ← readLoc fuel config.layout location | fault .shape
          publishOwner fuel config.layout location stored id org
      | none =>
          liftConstruction org (publishOperation [id])
          let value ← storedDestination id
          let receiving := pending.capability.layout
          bindRoot location.root (.stored { value with ty := receiving, destination := some id, object := some value.storage })
  | .replacement _ => fault .flow

mutual

def evalOp : Nat → Config → Func → Frame → Op → EvalM RVal
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, function, frame, op => do
    match op with
    | .render operand _ => pure (.rendered (← renderCell fuel config (← getCell frame operand)))
    | .constInt ty value => pure (.value (.int ty value))
    | .constBool value => pure (.value (.bool value))
    | .constUnit => pure (.value .unit)
    | .bin op ty left right org =>
        let (_,left) ← expectInt (← getValue frame left)
        let (_,right) ← expectInt (← getValue frame right)
        pure (.value (.int ty (← numeric org (Core.evalBin config.profile op ty left right))))
    | .un op ty operand org =>
        let (_,value) ← expectInt (← getValue frame operand)
        pure (.value (.int ty (← numeric org (Core.evalUn config.profile op ty value))))
    | .cmp op _ left right | .boolCmp op left right =>
        let (left,right) ← comparable (← getValue frame left) (← getValue frame right)
        pure (.value (.bool (Core.evalCmp op left right)))
    | .boolNot operand => pure (.value (.bool (!(← expectBool (← getValue frame operand)))))
    | .conv kind source target operand org =>
        let (_,value) ← expectInt (← getValue frame operand)
        pure (.value (.int target (← numeric org (Core.evalConv config.profile kind source target value))))
    | .next ty operand => pure (.value (.int ty ((← expectInt (← getValue frame operand)).2 + 1)))
    | .slotAddr id => pure (.value (.ref (← slotLoc function frame id)))
    | .globalAddr id => pure (.value (.ref ⟨.global id,[]⟩))
    | .refFreeze reference => pure (.value (← getValue frame reference))
    | .load reference => pure (.value (← readLoc fuel config.layout (← expectRef (← getValue frame reference))))
    | .snapshot _ reference =>
        let location ← expectRef (← getValue frame reference)
        pure (.view (← sample fuel config location) (some (← sourceOfLocation location)))
    | .sliceView id =>
        let .slice location start count ← getValue frame id | fault .shape
        pure (.view ⟨location,start,count,false⟩ frame.copySources[id]?)
    | .viewLen id => pure (.value (.int .i64 (← getView frame id).count))
    | .arrayLen reference =>
        let (count,_) ← arrayLength (← readLoc fuel config.layout (← expectRef (← getValue frame reference)))
        pure (.value (.int .i64 count))
    | .viewSlice _ id lo hi org =>
        let view ← getView frame id
        let lo ← arrayBound frame view.count 0 lo
        let hi ← arrayBound frame view.count view.count hi
        if lo < 0 || hi < lo || hi > view.count then abortAt .sliceOob (← origin org)
        pure (.value (.slice view.location (view.start + lo.toNat) (hi - lo).toNat))
    | .refElem view index | .indexProven view index =>
        pure (.value (.ref (← indexLocation (← getView frame view) (← expectInt (← getValue frame index)).2 false none)))
    | .indexChecked view index org =>
        pure (.value (.ref (← indexLocation (← getView frame view) (← expectInt (← getValue frame index)).2 true org)))
    | .fieldAddr owner index =>
        let location ← expectRef (← getValue frame owner)
        pure (.value (.ref ⟨location.root,location.path ++ [index]⟩))
    | .arrLit _ operands => pure (.value (.fixed (← operands.mapM (getValue frame)).toArray))
    | .arrFill ty operand =>
        let .arr _ count := ty | fault .shape
        pure (.value (.fixed (Array.replicate count (← getValue frame operand))))
    | .structLit ty operands =>
        let .structT id _ := ty | fault .shape
        pure (.value (.record id (← operands.mapM (getValue frame)).toArray))
    | .bytes bytes _ =>
        let scope ← freshScope
        let root := RootInst.global (config.module.globals.size + scope)
        bindStaticRoot root (.fixed (bytes.map (fun b => Value.int .u8 b.toNat)).toArray)
        pure (.value (.slice ⟨root,[]⟩ 0 bytes.length))
    | .push reference value org =>
        let location ← expectRef (← getValue frame reference)
        let (count,_) ← arrayLength (← readLoc fuel config.layout location)
        appendFixedValues fuel config.layout location [← getValue frame value] (← origin org)
        pure (.value (.ref ⟨location.root,location.path ++ [count]⟩))
    | .pop reference org =>
        let location ← expectRef (← getValue frame reference)
        let (count,_) ← arrayLength (← readLoc fuel config.layout location)
        if count == 0 then abortAt .popEmpty (← origin org)
        let value ← readLoc fuel config.layout ⟨location.root,location.path ++ [count - 1]⟩
        truncateOwner fuel config.layout location (count - 1) (← origin org)
        pure (.value value)
    | .result pack position =>
        let .pack carriers ← getCell frame pack | fault .shape
        let some carrier := carriers[position]? | fault .arity
        pure (packResults [carrier])
    | .destOpen receiver ty request count org =>
        let count ← count.mapM fun id => do
          let value := (← expectInt (← getValue frame id)).2
          if value < 0 then abortAt .capacity (← origin org)
          pure value.toNat
        let (id,snapshot) ← openReceiver fuel config function frame receiver ty request count (← origin org)
        pure (match snapshot with | some snapshot => .ownerExtension id snapshot | none => .dest id)
    | .destChild parent element org =>
        pure (.dest (← liftConstruction (← origin org) (openChild (← getDest frame parent) element (← receivingLayout config.layout element))))
    | .destAdapt destination producer _ org =>
        let id ← getDest frame destination
        liftConstruction (← origin org) (adaptDestinationType id producer)
        pure (.dest id)
    | .destAdaptFinish closed org =>
        let _ ← origin org
        match ← getCell frame closed with
        | .built id => pure (.built id)
        | .cancelled id => pure (.cancelled id)
        | .directCancelled id => pure (.directCancelled id)
        | _ => fault .shape
    | .destFinish destination org =>
        let id ← getDest frame destination
        let pending ← getDestination id
        if let some expected := pending.knownCount then
          unless progressCount pending.progress == some expected do fault .flow
        liftConstruction (← origin org) (finishDestination id)
        pure (.built id)
    | .destPrepareNamed destination slot org => do
        let id ← getDest frame destination
        let some localSlot := function.slots[slot]? | fault .unbound
        liftConstruction (← origin org) (prepareNamedBinding id localSlot.ty)
        pure (.dest id)
    | .destNamed slot _ =>
        let some id := frame.named.lookup slot | fault .unbound
        pure (.built (← completedDestination id))
    | .receivingOpen destination =>
        pure (.receiving (← getDest frame destination) frame.activation.act)
    | .targetReceiving target position org =>
        let _ ← origin org
        let some target := config.module.targets[target]? | fault .unbound
        let some activation := selectTarget? target (← EvalM.get).activations | fault .flow
        let some (.construct id) := activation.channels[position]? | fault .shape
        pure (.receiving id activation.act)
    | .exitWait receiver => do
        let (incoming,owner) ← getReceiving frame receiver
        unless owner == frame.activation.act do fault .flow
        let token ← liftProtocol (waitExitDestination incoming)
        pure (.waitingReservation token incoming owner receiver)
    | .destRenew receiver =>
        let (incoming,_) ← getReceiving frame receiver
        pure (.dest (← liftProtocol (renewReceivingDestination incoming)))
    | .destRefresh receiver previous =>
        let (incoming,_) ← getReceiving frame receiver
        let _ ← getDest frame previous
        pure (.dest (← liftProtocol (renewReceivingDestination incoming)))
    | .exitReserve receiver source org =>
        let (incoming,_) ← getReceiving frame receiver
        let coreSource ← match source with
          | .newValue => pure Goose.Construct.ExitSource.newValue
          | .namedAlias slot => do
              let some alias := frame.named.lookup slot | fault .unbound
              pure (if alias == (← receivingDestination incoming) then
                Goose.Construct.ExitSource.namedResult else .newValue)
        let (token,selected) ← liftConstruction (← origin org) (reserveExitDestination incoming coreSource)
        pure (.exitReservation (some token) selected incoming receiver (.reserved source) org)
    | .exitIsNamed ticket => do
        let (token,_,_,_,kind,_) ← getExitReservation frame ticket
        unless kind matches .reserved (.namedAlias _) do fault .flow
        let some token := token | fault .flow
        let state ← EvalM.get
        let isNamed := match state.construction.exitReservations[token]? with
          | some (.active (.named _) ..) => true
          | some (.active .fresh ..) => false
          | _ => false
        pure (.value (.bool isNamed))
    | .exitAdopt receiver built =>
        let (incoming,_) ← getReceiving frame receiver
        let built ← getBuilt frame built
        pure (.exitReservation none built incoming receiver .adopted none)
    | .reservedDest ticket =>
        let (token,selected,_,_,kind,_) ← getExitReservation frame ticket
        unless (match kind with
          | .reserved .newValue | .reserved (.namedAlias _) => true
          | _ => false) do fault .flow
        let some token := token | fault .flow
        let state ← EvalM.get
        unless (match state.construction.exitReservations[token]? with
          | some (.active .fresh ..) => true
          | _ => false) do fault .flow
        pure (.dest selected)
    | .reservedNamed ticket operationOrigin =>
        let (token,_,_,_,kind,_) ← getExitReservation frame ticket
        unless (match kind with | .reserved (.namedAlias _) => true | _ => false) do fault .flow
        let some token := token | fault .flow
        let state ← EvalM.get
        unless (match state.construction.exitReservations[token]? with
          | some (.active (.named .ready) ..) => true
          | _ => false) do fault .flow
        let selected ← liftConstruction (← origin operationOrigin) (materializeNamedReservation token)
        pure (.built (← completedDestination selected))
    | .exitLand ticket built org =>
        let (token,selected,incoming,_,kind,_) ← getExitReservation frame ticket
        let id ← getBuilt frame built
        let landing ← match kind,token with
          | .reserved _, some token => liftConstruction (← origin org) (landExitReservation token id)
          | .adopted, none => do
              unless id == selected do fault .flow
              if (← receivingDestination incoming) != id then
                liftConstruction (← origin org) (landExitReplacementInto incoming id)
              pure id
          | _, _ => fault .flow
        pure (.built landing)
    | .receivingCancel receiver carried org =>
        let (incoming,owner) ← getReceiving frame receiver
        let ids ← carried.mapM (getBuilt frame)
        let carriers := ids.map Carrier.completed
        let current ← receivingDestination incoming
        let sourceOrg ← origin org
        let cleanup := do
          if !ids.contains current then cleanupReceivingDestination sourceOrg incoming carriers
          restoreCompletedChildOwner frame incoming ids
        match frame.waitingCancelWitnesses.filter (·.1 == receiver) with
        | [(_,waitingTicket,token,protectedCarriers)] => do
            unless owner == frame.activation.act do fault .flow
            unless ids == protectedCarriers do fault .flow
            let state ← EvalM.get
            unless (match state.construction.exitReservations[token]? with
              | some .released => true
              | _ => false) do fault .flow
            let adopted : List DestinationId := frame.vals.toList.filterMap fun (valueId,value) =>
              match value with
              | .exitReservation none selected candidate candidateReceiver .adopted _ =>
                  if candidate == incoming && candidateReceiver == receiver &&
                      !frame.releasedAdoptedTickets.contains valueId &&
                      !frame.landedExitTickets.contains valueId then some selected else none
              | _ => none
            let selectedTickets := frame.vals.toList.filterMap fun (valueId,value) =>
              match value with
              | .exitReservation (some selectedToken) selected candidate candidateReceiver (.reserved _) _ =>
                  let active := match state.construction.exitReservations[selectedToken]? with
                    | some (.active ..) => true
                    | _ => false
                  if candidate == incoming && candidateReceiver == receiver && active then
                    some (valueId,selectedToken,selected) else none
              | _ => none
            let supersedingTicket := match selectedTickets with
              | [(_,selectedToken,_)] => some selectedToken
              | _ => none
            let exactSelection := match selectedTickets, ids with
              | [(_,selectedToken,selected)],_ =>
                  let active := match state.construction.exitReservations[selectedToken]? with
                    | some (.active _ selectedIncoming selectedDestination _) =>
                        selectedIncoming == incoming && selectedDestination == selected
                    | _ => false
                  let carriesSelection := ids.any fun built =>
                    match destinationCurrent state.construction selected,
                        state.construction.destinations[built]? with
                    | .ok resolved, some destination =>
                        built == resolved ||
                          (match exitLandingAnchor (state.construction.destinations.size + 1)
                              built destination.storage (some resolved) state.construction with
                            | .ok _ _ => true
                            | .fault _ _ => false)
                    | _, _ => false
                  active && carriesSelection
              | _,_ => false
            let unrelatedAuthority := frame.vals.toList.any fun (id,value) =>
              if id == waitingTicket then false else
              match value with
              | .waitingReservation token candidate _ candidateReceiver =>
                  candidate == incoming && candidateReceiver == receiver &&
                    !(frame.releasedWaitingTickets.contains id) &&
                    (state.construction.exitReservations[token]?).any (fun reservation => reservation matches .waiting ..)
              | .exitReservation (some selectedToken) _ candidate candidateReceiver _ _ =>
                  if candidateReceiver != receiver then false else
                  if candidate != incoming then false else
                  if exactSelection && supersedingTicket == some selectedToken then false else
                    match state.construction.exitReservations[selectedToken]? with
                    | some .released => false
                    | _ => true
              | .exitReservation none selected candidate candidateReceiver .adopted _ =>
                  candidateReceiver == receiver && candidate == incoming &&
                    !frame.releasedAdoptedTickets.contains id && !frame.landedExitTickets.contains id &&
                    !ids.contains selected
              | _ => false
            unless !unrelatedAuthority do fault .flow
            match exactSelection with
            | true => do
                cleanup
                pure (.directCancelled current)
            | false => do
                unless adopted.all ids.contains do fault .flow
                if adopted.isEmpty then pure (.directCancelled current) else do
                  let state ← EvalM.get
                  let selected := adopted.any fun built => built == current ||
                    (protectedReplacement? state.construction current [Carrier.completed built]).isSome
                  unless selected do fault .flow
                  cleanup
                  pure (.directCancelled current)
        | [] => do
            let destination ← getDestination current
            let state ← EvalM.get
            let direct := !activeProgress destination.progress || ids.contains current ||
              (protectedReplacement? state.construction current carriers).isSome
            cleanup
            pure (if direct then .directCancelled current else .cancelled current)
        | _ => fault .flow
    | .destAbandonNamed slot replacement org =>
        let some id := frame.named.lookup slot | fault .unbound
        let replacement ← getBuilt frame replacement
        if replacement == id then pure (.directCancelled id)
        else
          liftConstruction (← origin org) (abandonPreservingExit id replacement)
          pure (.cancelled id)
    | .destAbandon carrier org =>
        let cell ← getCell frame carrier
        let id ← getProtocol frame carrier
        let pending ← getDestination id
        let direct := match cell, pending.progress with
          | .dest found, .built _ => found == id && (frame.vals.toList.any fun (_, value) =>
              match value with | .built built => built == id | _ => false)
          | _, _ => false
        if direct then
          pure (.directCancelled id)
        else do
          match pending.progress with
          | .exiting _ replacement => liftConstruction (← origin org) (abandonPreservingExit id replacement)
          | _ => liftConstruction (← origin org) (abandonTree id)
          pure (.cancelled id)
    | .destPublishRef built org =>
        let id ← getBuilt frame built
        let location := (← getDestination id).capability.receiver
        let some owner := frame.pushOwners.lookup location | fault .flow
        publishDestination fuel config id (← origin org) (some owner)
        pure (.value (.ref location))
    | .destArg built org =>
        let id ← getBuilt frame built
        publishDestination fuel config id (← origin org)
        pure (.value (.ref (← getDestination id).capability.receiver))
    | .destValue destination org =>
        let id ← getDest frame destination
        let state ← EvalM.get
        let pending ← getDestination id
        let storage ← getStorage pending.storage
        let start := pending.capability.start
        let prefixPresent := pending.layout == .packed && pending.capability.request == .value
        let storage := if prefixPresent then storage else
          { storage with bytes := storage.bytes.extract 0 start ++ ⟨#[0,0,0,0]⟩ ++ storage.bytes.extract start storage.bytes.size }
        let capability := { pending.capability with request := .value }
        let pending := { pending with
          layout := .packed,
          capability := capability,
          writeEnd := pending.writeEnd + (if prefixPresent then 0 else 4) }
        EvalM.set { state with construction := { state.construction with storage := state.construction.storage.set! pending.storage storage, destinations := state.construction.destinations.set! id pending } }
        let _ ← origin org
        pure (.dest id)
    | .destRelocate built reason org =>
        let id ← getBuilt frame built
        match reason with
        | .headerRemoval =>
            liftConstruction (← origin org) (removeConstructionHeader id)
            let pending ← getDestination id
            liftConstruction (← origin org) (restoreReceivingLayout id (← receivingLayout config.layout pending.capability.layout))
        pure (.built id)
    | .destStage destination org =>
        let id ← getDest frame destination
        liftConstruction (← origin org) (stageDestination id)
        pure (.dest id)
    | .destFit built org =>
        let id ← getBuilt frame built
        liftConstruction (← origin org) (fitStagedDestination id)
        pure (.built id)
    | .call callee args org =>
        pure (packResults (← executeFn fuel config callee (← args.mapM (getValue frame)) [] (← origin org)))
    | .callConstruct callee args destinations org =>
        pure (packResults (← executeFn fuel config callee (← args.mapM (getValue frame)) (← destinations.mapM (getDest frame)) (← origin org)))

def evalEffect : Nat → Config → Func → Frame → Effect → EvalM Frame
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, function, frame, effect => do
    match effect with
    | .enter scope =>
        let scopeInst ← freshScope
        let activation := { frame.activation with scopes := (scope,scopeInst) :: frame.activation.scopes }
        setActivation activation
        if scope == 0 then
          for ((ty,ordinal),position) in (function.params.zip frame.parameterOrdinals).zipIdx do
            if (function.slots[position]?).any (fun slot => slot.scope == 0 && slot.ty == ty) then
              setObjectOrdinal (.local activation.act scopeInst position) ordinal
        pure { frame with activation }
    | .leave scope =>
        let some (current,scopeInst) := frame.activation.scopes.head? | fault .flow
        unless current == scope do fault .flow
        let activation := { frame.activation with scopes := frame.activation.scopes.tail }
        releaseScope activation scope scopeInst
        pure { frame with activation, named := frame.named.filter (fun (slot,_) => (function.slots[slot]?).any (·.scope != scope)) }
    | .slotInit slot value _ =>
        let location ← slotLoc function frame slot
        let value ← getValue frame value
        let value ← match value with
          | .ref incoming =>
              if (function.slots[slot]?).any (fun slot => slot.ty.nonfixed) then readLoc fuel config.layout incoming else pure value
          | _ => pure value
        bindRoot location.root value
        pure frame
    | .store reference value _ =>
        writeLoc fuel config.layout (← expectRef (← getValue frame reference)) (← getValue frame value)
        pure frame
    | .append reference view org =>
        appendRun fuel config.layout (← expectRef (← getValue frame reference)) (← getView frame view) (← origin org)
        pure frame
    | .appendValue reference value org =>
        let .fixed elements ← getValue frame value | fault .shape
        appendFixedValues fuel config.layout (← expectRef (← getValue frame reference)) elements.toList (← origin org)
        pure frame
    | .popN reference count org =>
        let location ← expectRef (← getValue frame reference)
        let count := (← expectInt (← getValue frame count)).2
        let (length,_) ← arrayLength (← readLoc fuel config.layout location)
        if count < 0 || count > length then abortAt .popNRange (← origin org)
        truncateOwner fuel config.layout location (length - count.toNat) (← origin org)
        pure frame
    | .clear reference org =>
        truncateOwner fuel config.layout (← expectRef (← getValue frame reference)) 0 (← origin org)
        pure frame
    | .resize reference size fill org =>
        let location ← expectRef (← getValue frame reference)
        let size := (← expectInt (← getValue frame size)).2
        if size < 0 then abortAt .resizeNegative (← origin org)
        let (length,_) ← arrayLength (← readLoc fuel config.layout location)
        if size.toNat <= length then truncateOwner fuel config.layout location size.toNat (← origin org)
        else
          let some fill := fill | abortAt .resizeFill (← origin org)
          appendFixedValues fuel config.layout location (List.replicate (size.toNat - length) (← getValue frame fill)) (← origin org)
        pure frame
    | .replace _ _ _ => fault .flow
    | .print parts _ =>
        let bytes ← parts.mapM fun
          | .text text => pure text.toUTF8
          | .val id => do renderCell fuel config (← getCell frame id)
        emitStdout ((bytes.foldl (· ++ ·) ByteArray.empty).push 10)
        pure frame
    | .destSnapshot destination snapshot org =>
        let id ← getDest frame destination
        let pending ← getDestination id
        let some element := pending.capability.logicalType.element? | fault .shape
        let .fixed values ← getValue frame snapshot | fault .shape
        for value in values do
          liftConstruction (← origin org) (writeElement id (← liftExcept (fixedBytes fuel config.layout element value)))
        pure frame
    | .destRepeat destination source org =>
        let id ← getDest frame destination
        let source ← getBuilt frame source
        let pending ← getDestination id
        let .arr element count := pending.capability.logicalType | fault .shape
        for _ in [0:count] do repeatElement fuel config.layout id element source (← origin org)
        liftConstruction (← origin org) (retireRepeatedSource id source)
        pure frame
    | .destWrite destination value org =>
        let destination ← getDest frame destination
        let pending ← getDestination destination
        let some element := pending.capability.logicalType.element? | fault .shape
        let bytes ← liftExcept (fixedBytes fuel config.layout element (← getValue frame value))
        liftConstruction (← origin org) (writeElement destination bytes)
        pure frame
    | .destAttach parent child org =>
        liftConstruction (← origin org) (attachChild (← getDest frame parent) (← getBuilt frame child))
        pure frame
    | .destBytes destination bytes org =>
        writeBytes (← getDest frame destination) ⟨bytes.toArray⟩ (← origin org)
        pure frame
    | .destText destination value org =>
        writeBytes (← getDest frame destination) (← renderCell fuel config (← getCell frame value)) (← origin org)
        pure frame
    | .destCopy destination source org =>
        let destination ← getDest frame destination
        let pending ← getDestination destination
        let some element := pending.capability.logicalType.element? | fault .shape
        let (view,copySource) ← match ← getCell frame source with
          | .view view source =>
              let some source := source | fault .unbound
              pure (view,source)
          | .value (.ref location) => do
              let source ← sourceOfLocation location
              let view ← match ← readLoc fuel config.layout location with
                | .slice backing start count => pure ⟨backing,start,count,false⟩
                | _ => sample fuel config location
              pure (view,source)
          | .copied (.slice location start count) source => pure (⟨location,start,count,false⟩,source)
          | .value (.slice location start count) =>
              let some source := frame.copySources[source]? | fault .unbound
              pure (⟨location,start,count,false⟩,source)
          | _ => fault .shape
        liftConstruction (← origin org) (recordCopy copySource destination)
        for index in [0:view.count] do
          let value ← readLoc fuel config.layout ⟨view.location.root,view.location.path ++ [view.start + index]⟩
          let bytes ← if element.nonfixed then do
              let .stored stored := value | fault .shape
              let storage ← getStorage stored.storage
              let finish ← liftLayout (packedEnd fuel config.layout element storage.bytes stored.start)
              pure (storage.bytes.extract stored.start finish)
            else liftExcept (fixedBytes fuel config.layout element value)
          liftConstruction (← origin org) (writeElement destination bytes)
        pure frame
    | .destBind slot built _ =>
        let id ← getBuilt frame built
        let value ← storedDestination id
        let location ← slotLoc function frame slot
        let some descriptor := function.slots[slot]? | fault .unbound
        let object ← reserveRootObject location.root
        bindRoot location.root (.stored { value with ty := descriptor.ty, object := some object })
        pure { frame with named := (slot,id) :: frame.named }
    | .destPublish built org =>
        let id ← getBuilt frame built
        publishDestination fuel config id (← origin org) (frame.pushOwners.lookup (← getDestination id).capability.receiver)
        pure frame
    | .destCancel cancelled org =>
        match ← getCell frame cancelled with
        | .cancelled id => liftConstruction (← origin org) (acknowledgeAbandonment id)
        | .directCancelled _ => pure ()
        | _ => fault .shape
        let _ ← origin org
        pure frame
    | .receivingDrop receiving =>
        let _ ← getReceiving frame receiving
        pure frame
    | .exitRelease ticket org =>
        let _ ← origin org
        match ← getCell frame ticket with
        | .waitingReservation token _ owner _ => do
            unless owner == frame.activation.act && !frame.releasedWaitingTickets.contains ticket do fault .flow
            liftProtocol (releaseExitReservation token)
            pure { frame with
              waitingReceipts := frame.waitingReceipts.filter (·.1 != ticket)
              releasedWaitingTickets := ticket :: frame.releasedWaitingTickets
              terminalWaitingRelease := true }
        | .exitReservation (some token) .. => do
            unless !frame.terminalWaitingRelease do fault .flow
            liftProtocol (releaseExitReservation token)
            pure { frame with waitingReceipts := frame.waitingReceipts.filter (·.1 != ticket) }
        | .exitReservation none .. => do
            let (_,_,_,_,kind,_) ← getExitReservation frame ticket
            unless kind == .adopted && frame.landedExitTickets.contains ticket &&
                !frame.releasedAdoptedTickets.contains ticket && !frame.terminalWaitingRelease do
              fault .flow
            pure { frame with releasedAdoptedTickets := ticket :: frame.releasedAdoptedTickets }
        | _ => fault .shape
    | .exitRearm ticket org => do
        let _ ← origin org
        let (token,incoming,owner,receiver) ← match ← getCell frame ticket with
          | .exitReservation (some token) _ incoming receiver (.reserved _) _ =>
              pure (token,incoming,frame.activation.act,receiver)
          | _ => fault .flow
        unless frame.waitingTickets.any (·.1 == ticket) &&
            !frame.releasedWaitingTickets.contains ticket && !frame.terminalWaitingRelease &&
            !frame.landedExitTickets.contains ticket do
          fault .flow
        let (receiverIncoming,receiverOwner) ← getReceiving frame receiver
        unless receiverIncoming == incoming && receiverOwner == owner do fault .flow
        let some (_,receipt) := frame.waitingReceipts.find? (·.1 == ticket) | fault .flow
        unless receipt.token == token && receipt.incoming == incoming do fault .flow
        let state ← EvalM.get
        unless (state.construction.exitReservations[token]?).any (fun reservation =>
            match reservation with
            | .active _ activeIncoming _ _ => activeIncoming == incoming
            | .restored => true
            | _ => false) do
          fault .flow
        liftProtocol (cancelExitReservation token [])
        liftProtocol (rearmExitReservation receipt)
        let waiting : RVal := .waitingReservation token incoming owner receiver
        pure { frame with vals := frame.vals.insert ticket waiting }
    | .exitSelect ticket source org => do
        let (token,incoming,owner,receiver) ← getWaitingExitReservation frame ticket
        unless owner == frame.activation.act do fault .flow
        let selectedSource ← match source with
          | .newValue => pure Goose.Construct.ExitSource.newValue
          | .namedAlias slot => do
              let some alias := frame.named.lookup slot | fault .unbound
              pure (if alias == (← receivingDestination incoming) then
                Goose.Construct.ExitSource.namedResult else .newValue)
        let selected ← liftConstruction (← origin org) (selectWaitingExitDestination token selectedSource)
        let value := .exitReservation (some token) selected incoming receiver (.reserved source) org
        pure { frame with vals := frame.vals.insert ticket value }
    | .exitMarkNamed ticket org =>
        let (token,selected,_,_,kind,_) ← getExitReservation frame ticket
        let .reserved (.namedAlias slot) := kind | fault .flow
        let some token := token | fault .flow
        unless frame.named.lookup slot == some selected do fault .flow
        liftConstruction (← origin org) (markNamedReservation token)
        pure frame
    | .exitDiscard ticket carried org =>
        match ← getCell frame ticket with
        | .waitingReservation token _ owner receiver => do
            unless owner == frame.activation.act do fault .flow
            let carried ← carried.mapM (getBuilt frame)
            liftConstruction (← origin org) do
              cancelExitReservation token carried
              releaseExitReservation token
            pure { frame with
              waitingCancelWitnesses := (receiver,ticket,token,carried) :: frame.waitingCancelWitnesses
              waitingReceipts := frame.waitingReceipts.filter (·.1 != ticket) }
        | .exitReservation (some token) _ _ _ kind _ => do
            unless kind matches .reserved .. do fault .flow
            let carried ← carried.mapM (getBuilt frame)
            liftConstruction (← origin org) do
              cancelExitReservation token carried
              releaseExitReservation token
            pure { frame with waitingReceipts := frame.waitingReceipts.filter (·.1 != ticket) }
        | _ => fault .shape

def executeInsts : Nat → Config → Func → Frame → List Inst → EvalM ExecOutcome
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, function, frame, instructions => do
    if frame.terminalWaitingRelease then
      match instructions with
      | .eff (.exitRelease ticket _) :: _ =>
          unless !frame.releasedWaitingTickets.contains ticket do fault .flow
          match ← getCell frame ticket with
          | .waitingReservation _ _ owner _ => unless owner == frame.activation.act do fault .flow
          | _ => fault .flow
      | .term (.abort ..) :: _ | .term (.exit ..) :: _ | .term .unreachable :: _ =>
          unless frame.waitingTickets.all (fun (ticket,_) => frame.releasedWaitingTickets.contains ticket) do
            fault .flow
      | _ => fault .flow
    match instructions with
    | [] => fault .flow
    | .def result op :: rest =>
        let value ← evalOp fuel config function frame op
        let (value,ownerExtensionSnapshots) := match value with
          | .ownerExtension id snapshot => (RVal.dest id,(id,snapshot) :: frame.ownerExtensionSnapshots)
          | _ => (value,frame.ownerExtensionSnapshots)
        let copySource ← match op with
          | .load reference => do
              match value with
              | .value (.slice ..) => pure (some (← sourceOfLocation (← expectRef (← getValue frame reference))))
              | _ => pure none
          | .viewSlice _ source _ _ _ => do
              let .view _ source ← getCell frame source | fault .shape
              pure source
          | _ => pure none
        let receivers ← match op, value with
          | .destOpen (.push reference) .., .dest id => do
              pure (((← getDestination id).capability.receiver, ← expectRef (← getValue frame reference)) :: frame.pushOwners)
          | _, _ => pure frame.pushOwners
        let sources := match copySource with | some source => frame.copySources.insert result source | none => frame.copySources.erase result
        let nextFrame := match op, value with
          | .exitWait _, .waitingReservation token .. =>
              { frame with waitingTickets := (result,token) :: frame.waitingTickets, ownerExtensionSnapshots := ownerExtensionSnapshots }
          | _, _ => { frame with ownerExtensionSnapshots := ownerExtensionSnapshots }
        let nextFrame := match op with
          | .exitLand ticket .. =>
              { nextFrame with landedExitTickets := ticket :: nextFrame.landedExitTickets }
          | .receivingCancel receiver .. =>
              { nextFrame with waitingCancelWitnesses := nextFrame.waitingCancelWitnesses.filter (·.1 != receiver) }
          | _ => nextFrame
        let waitingReceipts ← match op,value with
          | .exitWait _, .waitingReservation token .. => do
              let state ← EvalM.get
              let some receipt := captureWaitingExitReservation token state.construction | fault .flow
              pure ((result,receipt) :: frame.waitingReceipts.filter (·.1 != result))
          | _, _ => pure frame.waitingReceipts
        executeInsts fuel config function {
          nextFrame with
          vals := nextFrame.vals.insert result value
          copySources := sources
          pushOwners := receivers
          waitingReceipts } rest
    | .eff effect :: rest =>
        executeInsts fuel config function (← evalEffect fuel config function frame effect) rest
    | .term term :: _ => match term with
      | .br target args => executeBlock fuel config function frame target (← args.mapM (getCell frame))
      | .condbr condition left la right ra =>
          let condition ← expectBool (← getValue frame condition)
          executeBlock fuel config function frame (if condition then left else right) (← (if condition then la else ra).mapM (getCell frame))
      | .ret results _ => pure (.returned (← results.mapM (getCarrier frame)))
      | .abort kind org => abortAt kind (← origin org)
      | .exit value _ => EvalM.stop (.exit (← expectInt (← getValue frame value)).2)
      | .unreachable => fault .flow
      | .escape targetId results cancellations _ =>
          let some target := config.module.targets[targetId]? | fault .unbound
          let some activation := selectTarget? target (← EvalM.get).activations | fault .flow
          let carriers ← results.mapM (getCarrier frame)
          let cancellations ← cancellations.mapM (getCell frame)
          pure (.escaped ⟨activation.act,.nonlocal targetId⟩ carriers cancellations)
      | .invoke callee args destinations normal forwarded escapes org =>
          let arguments ← args.mapM (getValue frame)
          let destinations ← destinations.mapM (getDest frame)
          let forwarded ← forwarded.mapM (getCell frame)
          let org ← origin org
          fun state =>
            match executeFnOutcome fuel config callee arguments destinations org state with
            | .ok (.returned results) state => executeBlock fuel config function frame normal ((results.map fun carrier => packResults [carrier]) ++ forwarded) state
            | .ok (.escaped address results cancellations) state =>
                match address.target with
                | .ordinary => .stop (.fault .flow) state
                | .nonlocal targetId =>
                    match state.activations.find? (fun activation => activation.act == address.activation) with
                    | none => .stop (.fault .flow) state
                    | some activation =>
                        if !(config.module.targets[targetId]?).any (fun target => target.contains activation.implementation) then
                          .stop (.fault .flow) state
                        else match escapes.find? (fun edge => edge.target == targetId) with
                        | none => .stop (.fault .flow) state
                        | some edge =>
                            let leading := results.map (fun carrier => packResults [carrier]) ++ cancellations
                            (do executeBlock fuel config function frame edge.block (leading ++ (← edge.args.mapM (getCell frame)))) state
            | .escape _ _ state => .stop (.fault .flow) state
            | .stop stop state => .stop stop state
            | .jump target kind state => .jump target kind state

def executeBlock : Nat → Config → Func → Frame → BlockId → List RVal → EvalM ExecOutcome
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, function, frame, block, arguments => do
    let some block := function.blocks[block]? | fault .unbound
    executeInsts fuel config function (← bindParams frame block.params arguments) block.insts

def executeFnOutcome : Nat → Config → FnId → List Value → List DestinationId → OriginId → EvalM ExecOutcome
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, functionId, arguments, destinations, org => do
    let some function := config.module.funcs[functionId]? | fault .unbound
    executeFunctionOutcome fuel config functionId function arguments destinations org

def executeFunctionOutcome : Nat → Config → FnId → Func → List Value → List DestinationId → OriginId → EvalM ExecOutcome
  | 0, _, _, _, _, _, _ => timeout
  | fuel + 1, config, functionId, function, arguments, destinations, org => do
    unless arguments.length == function.params.length do fault .arity
    let act ← freshAct
    let mut parameterOrdinals : List StorageId := []
    for (ty,value) in function.params.zip arguments do
      let ordinal ← if ty.nonfixed then do
          let location ← expectRef value
          let some ordinal := (← EvalM.get).objectOrdinals.lookup location.root | fault .unbound
          pure ordinal
        else liftConstruction org reserveStorage
      parameterOrdinals := parameterOrdinals ++ [ordinal]
    let mut destinationIds := destinations
    let mut channels : List Channel := []
    for descriptor in function.results do
      let channel ← match descriptor.request with
        | .register => pure (Channel.register descriptor.ty)
        | .value | .elementRun => do
            let id :: rest := destinationIds | fault .arity
            destinationIds := rest
            pure (.construct id)
      channels := channels ++ [channel]
    unless destinationIds.isEmpty do fault .arity
    let vars := function.slots.map fun slot => ({ name := "", ty := slot.ty, kind := slot.kind, scope := slot.scope, org } : LocalVar)
    let activation : RuntimeActivation := ⟨functionId,act,vars,[],channels⟩
    let state ← EvalM.get
    EvalM.set { state with activations := activation :: state.activations }
    let frame : Frame := { function := functionId, activation, parameterOrdinals }
    let arguments := (arguments.zip function.params |>.zip parameterOrdinals).map (fun ((value,ty),ordinal) =>
      if ty matches .slice .. then RVal.copied value (.storage ordinal []) else RVal.value value) ++ destinations.map RVal.dest
    fun state =>
      let removeActivation (state : ExecutionState) :=
        { state with activations := state.activations.filter (fun activation => activation.act != act) }
      let firstReservation := state.construction.exitReservations.size
      match executeBlock fuel config function frame 0 arguments state with
      | .stop reason stopped =>
          match releaseReservationsForStop firstReservation stopped with
          | .ok () cleaned => .stop reason (removeActivation cleaned)
          | .stop cleanupReason cleaned => .stop cleanupReason (removeActivation cleaned)
          | .escape _ _ cleaned | .jump _ _ cleaned => .stop (.fault .flow) (removeActivation cleaned)
      | .ok outcome state =>
          let state := removeActivation state
          let finish carriers state :=
            match finishChannels config.layout activation.channels
                (function.results.map (·.ty)) carriers org state with
            | .ok () finished => ExecutionStep.ok
                (match outcome with
                | .returned _ => .returned carriers
                | .escaped address _ cancellations => .escaped address carriers cancellations)
                finished
            | .stop reason failed => .stop reason failed
            | .escape target carriers failed => .escape target carriers failed
            | .jump target kind failed => .jump target kind failed
          match outcome with
          | .returned carriers => finish carriers state
          | .escaped address carriers cancellations =>
              if address.activation == act then finish carriers state
              else .ok (.escaped address carriers cancellations) state
      | .escape _ _ state => .stop (.fault .flow) (removeActivation state)
      | .jump target kind state => .jump target kind (removeActivation state)

def executeFn (fuel : Nat) (config : Config) (functionId : FnId) (arguments : List Value)
    (destinations : List DestinationId) (org : OriginId) : EvalM (List Carrier) := do
  match ← executeFnOutcome fuel config functionId arguments destinations org with
  | .returned carriers => pure carriers
  | .escaped .. => fault .flow

def executeFunction (fuel : Nat) (config : Config) (functionId : FnId) (function : Func)
    (arguments : List Value) (destinations : List DestinationId) (org : OriginId) : EvalM (List Carrier) := do
  match ← executeFunctionOutcome fuel config functionId function arguments destinations org with
  | .returned carriers => pure carriers
  | .escaped .. => fault .flow
end

end Goose.Construct.GIR
