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
  | built (id : DestinationId)
  | cancelled (id : DestinationId)
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
  elementReceivers : List (DestinationId × Loc) := []

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
    (receiver : DestReceiver) (logical : Ty) (request : Core.ConstructionRequest) (count : Option Nat) (org : OriginId) : EvalM DestinationId := do
  let fresh (location : Loc) (receiving : Ty) : EvalM DestinationId := do
    let storage ← reserveRootObject location.root
    let capability : Core.Destination Ty := ⟨0,location,receiving,logical,request,0,frame.activation.act⟩
    liftConstruction org (openDestinationDirect storage capability (← receivingLayout config.layout receiving) count)
  match receiver with
  | .slot slot => do
      let some descriptor := function.slots[slot]? | fault .unbound
      fresh (← slotLoc function frame slot) descriptor.ty
  | .global global => do
      let some descriptor := config.module.globals[global]? | fault .unbound
      fresh ⟨.global global,[]⟩ descriptor.ty
  | .arg _ position => do
      let scope ← freshScope
      fresh ⟨.local frame.activation.act scope (function.slots.size + position),[]⟩ logical
  | .append reference | .whole reference => do
      let location ← expectRef (← getValue frame reference)
      if receiver matches .whole _ then truncateOwner fuel config.layout location 0 org
      let .stored stored ← readLoc fuel config.layout location | fault .shape
      let id ← ownerDestination config.layout stored request count org
      let state ← EvalM.get
      let some pending := state.construction.destinations[id]? | fault .unbound
      let pending := { pending with capability := { pending.capability with receiver := location, logicalType := logical } }
      EvalM.set { state with construction := { state.construction with destinations := state.construction.destinations.set! id pending } }
      pure id
  | .push reference => do
      let location ← expectRef (← getValue frame reference)
      let .stored stored ← readLoc fuel config.layout location | fault .shape
      openElementReceiving config.layout frame.activation.act location stored logical count org

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
        pure (.dest (← openReceiver fuel config function frame receiver ty request count (← origin org)))
    | .destChild parent element org =>
        pure (.dest (← liftConstruction (← origin org) (openChild (← getDest frame parent) element (← receivingLayout config.layout element))))
    | .destFinish destination org =>
        let id ← getDest frame destination
        let pending ← getDestination id
        if let some expected := pending.knownCount then
          unless progressCount pending.progress == some expected do fault .flow
        liftConstruction (← origin org) (finishDestination id)
        pure (.built id)
    | .destNamed slot _ =>
        let some id := frame.named.lookup slot | fault .unbound
        pure (.built (← completedDestination id))
    | .resultExitDest position org =>
        let some (.construct id) := frame.activation.channels[position]? | fault .shape
        pure (.dest (← liftConstruction (← origin org) (openExitReplacement id)))
    | .targetDest target position org =>
        let some target := config.module.targets[target]? | fault .unbound
        let some activation := selectTarget? target (← EvalM.get).activations | fault .flow
        let some (.construct id) := activation.channels[position]? | fault .shape
        pure (.dest (← liftConstruction (← origin org) (openExitReplacement id)))
    | .destAbandonNamed slot replacement org =>
        let some id := frame.named.lookup slot | fault .unbound
        liftConstruction (← origin org) (abandonPreservingExit id (← getBuilt frame replacement))
        pure (.cancelled id)
    | .destAbandon carrier org =>
        let id ← getProtocol frame carrier
        let pending ← getDestination id
        match pending.progress with
        | .exiting _ replacement => liftConstruction (← origin org) (abandonPreservingExit id replacement)
        | _ => liftConstruction (← origin org) (abandonTree id)
        pure (.cancelled id)
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
        let storage := { storage with bytes := storage.bytes.extract 0 start ++ ⟨#[0,0,0,0]⟩ ++ storage.bytes.extract start storage.bytes.size }
        let pending := { pending with layout := .packed, capability := { pending.capability with request := .value }, writeEnd := pending.writeEnd + 4 }
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
        | .exitValue => liftConstruction (← origin org) (landExitReplacement id)
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
        publishDestination fuel config id (← origin org) (frame.elementReceivers.lookup id)
        pure frame
    | .destCancel cancelled org =>
        let .cancelled id ← getCell frame cancelled | fault .shape
        liftConstruction (← origin org) (acknowledgeAbandonment id)
        pure frame

def executeInsts : Nat → Config → Func → Frame → List Inst → EvalM (List Carrier)
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, function, frame, instructions => do
    match instructions with
    | [] => fault .flow
    | .def result op :: rest =>
        let value ← evalOp fuel config function frame op
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
              pure ((id, ← expectRef (← getValue frame reference)) :: frame.elementReceivers)
          | _, _ => pure frame.elementReceivers
        let sources := match copySource with | some source => frame.copySources.insert result source | none => frame.copySources.erase result
        executeInsts fuel config function { frame with vals := frame.vals.insert result value, copySources := sources, elementReceivers := receivers } rest
    | .eff effect :: rest =>
        executeInsts fuel config function (← evalEffect fuel config function frame effect) rest
    | .term term :: _ => match term with
      | .br target args => executeBlock fuel config function frame target (← args.mapM (getCell frame))
      | .condbr condition left la right ra =>
          let condition ← expectBool (← getValue frame condition)
          executeBlock fuel config function frame (if condition then left else right) (← (if condition then la else ra).mapM (getCell frame))
      | .ret results _ => results.mapM (getCarrier frame)
      | .abort kind org => abortAt kind (← origin org)
      | .exit value _ => EvalM.stop (.exit (← expectInt (← getValue frame value)).2)
      | .unreachable => fault .flow
      | .escape targetId results _ _ =>
          let some target := config.module.targets[targetId]? | fault .unbound
          let some activation := selectTarget? target (← EvalM.get).activations | fault .flow
          let carriers ← results.mapM (getCarrier frame)
          fun state => .escape ⟨activation.act,.nonlocal targetId⟩ carriers state
      | .invoke callee args destinations normal forwarded escapes org =>
          let arguments ← args.mapM (getValue frame)
          let destinations ← destinations.mapM (getDest frame)
          let forwarded ← forwarded.mapM (getCell frame)
          let org ← origin org
          fun state =>
            match executeFn fuel config callee arguments destinations org state with
            | .ok results state => executeBlock fuel config function frame normal ((results.map fun carrier => packResults [carrier]) ++ forwarded) state
            | .escape address results state =>
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
                            let leading := results.map (fun carrier => packResults [carrier]) ++ destinations.map RVal.cancelled
                            (do executeBlock fuel config function frame edge.block (leading ++ (← edge.args.mapM (getCell frame)))) state
            | .stop stop state => .stop stop state
            | .jump target kind state => .jump target kind state

def executeBlock : Nat → Config → Func → Frame → BlockId → List RVal → EvalM (List Carrier)
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, function, frame, block, arguments => do
    let some block := function.blocks[block]? | fault .unbound
    executeInsts fuel config function (← bindParams frame block.params arguments) block.insts

def executeFn : Nat → Config → FnId → List Value → List DestinationId → OriginId → EvalM (List Carrier)
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, functionId, arguments, destinations, org => do
    let some function := config.module.funcs[functionId]? | fault .unbound
    executeFunction fuel config functionId function arguments destinations org

def executeFunction : Nat → Config → FnId → Func → List Value → List DestinationId → OriginId → EvalM (List Carrier)
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
    fun state => mapStepState (fun state => { state with activations := state.activations.filter (fun activation => activation.act != act) })
      (executeBlock fuel config function frame 0 arguments state)
end

end Goose.Construct.GIR
