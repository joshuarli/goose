import Goose.Construct.Value

namespace Goose.Construct
open Goose.Core (ActId ScopeInst RootInst Loc StorageId DestinationId VarId GlobalId ContextId OriginId IntTy NumProfile AbortKind FaultKind BinOp)

def fault (kind : FaultKind) : EvalM α := EvalM.stop (.fault kind)
def timeout : EvalM α := EvalM.stop .timeout
def abortAt (kind : AbortKind) (origin : OriginId) : EvalM α := EvalM.stop (.abort kind origin)

def liftExcept (action : Except Core.Stop α) : EvalM α :=
  match action with
  | .ok value => pure value
  | .error reason => EvalM.stop reason

def liftLayout (action : Except LayoutFault α) : EvalM α :=
  match action with
  | .ok value => pure value
  | .error .bounds => fault .pathRange
  | .error .type => fault .shape
  | .error .fuel => timeout

def getDestination (id : DestinationId) : EvalM PendingDestination := do
  match (← EvalM.get).construction.destinations[id]? with
  | some destination => pure destination
  | none => fault .unbound

def getStorage (id : StorageId) : EvalM ReceivingStorage := do
  match (← EvalM.get).construction.storage[id]? with
  | some storage => pure storage
  | none => fault .danglingRoot

def progressCount : DestinationProgress → Option Nat
  | .open count | .built count | .published count | .attached count => some count
  | .suspended count _ | .exiting count _ => some count
  | .abandoned | .cancelled | .retired => none

def storedDestination (id : DestinationId) : EvalM StoredValue := do
  let destination ← getDestination id
  let some count := progressCount destination.progress | fault .flow
  let storage := match destination.progress with
    | .published _ => destination.backing.receiverStorage
    | _ => destination.storage
  pure ⟨storage, destination.capability.start,
    destination.capability.logicalType, count, some id, none, [], count⟩

def elementType : Ty → Option Ty
  | .arr element _ | .varr element | .grow element | .growshrink element | .limited element _ => some element
  | _ => none

def receivingLayout (module : LayoutEnv) : Ty → EvalM ReceivingLayout
  | .varr _ => pure .packed
  | .arr _ count => pure (.fixed count)
  | .limited element capacity =>
      match fixedByteSize? module element with
      | some width => pure (.limited capacity width)
      | none => fault .shape
  | .grow _ | .growshrink _ => pure .elements
  | _ => fault .shape

def intBytes (ty : IntTy) (value : Int) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  let bits := Core.toBits ty value
  for index in [0:ty.bits / 8] do
    bytes := bytes.push (UInt8.ofNat ((bits.toNat / 2 ^ (index * 8)) % 256))
  return bytes

def bytesInt (ty : IntTy) (bytes : ByteArray) (start : Nat) : Except FaultKind Int := do
  if start + ty.bits / 8 > bytes.size then throw .pathRange
  let mut bits := 0
  for index in [0:ty.bits / 8] do
    let some byte := bytes.data[start + index]? | throw .pathRange
    bits := bits + byte.toNat * 2 ^ (8 * index)
  pure (Core.ofBits ty bits)

def fixedBytes : Nat → LayoutEnv → Ty → Value → Except Core.Stop ByteArray
  | 0, _, _, _ => .error .timeout
  | fuel + 1, module, ty, value => do
    match ty, value with
    | .int ty, .int actual value =>
        if ty == actual then .ok (intBytes ty value) else .error (.fault .shape)
    | .bool, .bool value => .ok ⟨#[if value then 1 else 0]⟩
    | .arr element count, .fixed elements => do
        if elements.size != count then throw (.fault .shape)
        let parts ← elements.toList.mapM (fixedBytes fuel module element)
        pure (parts.foldl (· ++ ·) ByteArray.empty)
    | .structT id _, .record actual fields => do
        if id != actual then throw (.fault .shape)
        let some descriptor := module.structs[id]? | throw (.fault .unbound)
        if descriptor.fields.size != fields.size then throw (.fault .shape)
        let mut bytes : ByteArray := ⟨Array.replicate descriptor.byteSize 0⟩
        for (field, value) in descriptor.fields.toList.zip fields.toList do
          let part ← fixedBytes fuel module field.ty value
          if field.byteOffset + part.size > bytes.size then throw (.fault .pathRange)
          for index in [0:part.size] do
            let some byte := part.data[index]? | throw (.fault .pathRange)
            bytes := bytes.set! (field.byteOffset + index) byte
        pure bytes
    | _, _ => .error (.fault .shape)
  

def fixedValue (fuel : Nat) (module : LayoutEnv) (ty : Ty) (bytes : ByteArray) (start : Nat) : Except Core.Stop Value :=
  match fuel with
  | 0 => .error .timeout
  | fuel + 1 => do
      match ty with
      | .int ty => pure (.int ty (← (bytesInt ty bytes start).mapError Core.Stop.fault))
      | .bool =>
          let some byte := bytes.data[start]? | throw (.fault .pathRange)
          pure (.bool (byte != 0))
      | .arr element count =>
          let some width := fixedByteSize? module element | throw (.fault .shape)
          let elements ← (List.range count).mapM fun index => fixedValue fuel module element bytes (start + index * width)
          pure (.fixed elements.toArray)
      | .structT id _ =>
          let some descriptor := module.structs[id]? | throw (.fault .unbound)
          let fields ← descriptor.fields.toList.mapM fun field => fixedValue fuel module field.ty bytes (start + field.byteOffset)
          pure (.record id fields.toArray)
      | _ => throw (.fault .shape)

def sampledStored (stored : StoredValue) : EvalM (ByteArray × SampledRun) := do
  let bytes := (← getStorage stored.storage).bytes
  let count ← match stored.destination with
    | none => pure stored.count
    | some id => do
        let destination ← getDestination id
        match destination.progress with
        | .published _ => pure (← getStorage stored.storage).publishedCount
        | progress =>
            let some count := progressCount progress | fault .danglingRoot
            pure count
  let some element := elementType stored.ty | fault .shape
  let headerSize ← match stored.destination with
    | some id => do
        let destination ← getDestination id
        pure (if destination.layout == .packed && destination.capability.request == .value then 4 else 0)
    | none => pure (match stored.ty with | .varr _ => 4 | _ => 0)
  pure (bytes, ⟨stored.start + headerSize, count, element⟩)

def storedPathRun (stored : StoredValue) : EvalM (ByteArray × SampledRun) := do
  let (bytes, run) ← sampledStored stored
  pure (bytes, { run with count := match stored.ty with
    | .limited _ _ => stored.writtenCount
    | _ => run.count })

def readStoredElement (fuel : Nat) (module : LayoutEnv) (stored : StoredValue) (index : Nat) : EvalM Value := do
  let (bytes, run) ← storedPathRun stored
  let (start, _) ← liftLayout (elementInterval fuel module bytes run index)
  if run.element.nonfixed then
    let sampled ← liftLayout (samplePacked run.element bytes start)
    pure (.stored ⟨stored.storage, start, run.element, sampled.count, none, some (stored.object.getD stored.storage), stored.path ++ [index], sampled.count⟩)
  else liftExcept (fixedValue fuel module run.element bytes start)

def readValuePath : Nat → LayoutEnv → Value → List Nat → EvalM Value
  | 0, _, _, _ => timeout
  | _ + 1, _, value, [] => pure value
  | fuel + 1, module, value, index :: rest => do
      let child ← match value with
        | .fixed elements | .record _ elements =>
            match elements[index]? with
            | some child => pure child
            | none => fault .pathRange
        | .stored stored => readStoredElement fuel module stored index
        | _ => fault .shape
      readValuePath fuel module child rest

def readLoc (fuel : Nat) (module : LayoutEnv) (location : Loc) : EvalM Value := do
  match (← EvalM.get).objects.lookup location.root with
  | some value => readValuePath fuel module value location.path
  | none => fault .danglingRoot

def setObjectOrdinal (root : RootInst) (ordinal : StorageId) : EvalM Unit := do
  let state ← EvalM.get
  EvalM.set { state with objectOrdinals := (root, ordinal) :: state.objectOrdinals.filter (fun entry => entry.1 != root) }

def reserveRootObject (root : RootInst) : EvalM StorageId := do
  let state ← EvalM.get
  match state.objectOrdinals.lookup root with
  | some ordinal => pure ordinal
  | none =>
      let ordinal ← liftConstruction 0 reserveStorage
      setObjectOrdinal root ordinal
      pure ordinal

def bindStaticRoot (root : RootInst) (value : Value) : EvalM Unit := do
  let state ← EvalM.get
  EvalM.set { state with objects := (root, value) :: state.objects.filter (fun entry => entry.1 != root) }

def bindRoot (root : RootInst) (value : Value) : EvalM Unit := do
  if ((← EvalM.get).objectOrdinals.lookup root).isNone then
    match value with
    | .stored stored => setObjectOrdinal root (stored.object.getD stored.storage)
    | _ => let _ ← reserveRootObject root; pure ()
  bindStaticRoot root value

def writeValuePath : Nat → LayoutEnv → Value → List Nat → Value → EvalM Value
  | 0, _, _, _, _ => timeout
  | _ + 1, _, _, [], replacement => pure replacement
  | fuel + 1, module, value, index :: rest, replacement => do
      match value with
      | .fixed elements =>
          let some child := elements[index]? | fault .pathRange
          let child ← writeValuePath fuel module child rest replacement
          pure (.fixed (elements.set! index child))
      | .record id fields =>
          let some child := fields[index]? | fault .pathRange
          let child ← writeValuePath fuel module child rest replacement
          pure (.record id (fields.set! index child))
      | .stored stored =>
          let (bytes, run) ← storedPathRun stored
          let (start, finish) ← liftLayout (elementInterval fuel module bytes run index)
          let child ← readStoredElement fuel module stored index
          if run.element.nonfixed then
            if rest.isEmpty then fault .shape
            let _ ← writeValuePath fuel module child rest replacement
            pure value
          else
            let replacement ← writeValuePath fuel module child rest replacement
            let part ← liftExcept (fixedBytes fuel module run.element replacement)
            if start + part.size != finish then fault .shape
            let state ← EvalM.get
            let some storage := state.construction.storage[stored.storage]? | fault .danglingRoot
            let bytes := bytes.extract 0 start ++ part ++ bytes.extract finish bytes.size
            let construction := { state.construction with storage := state.construction.storage.set! stored.storage { storage with bytes := bytes } }
            EvalM.set { state with construction := construction }
            pure value
      | _ => fault .shape

def writeLoc (fuel : Nat) (module : LayoutEnv) (location : Loc) (replacement : Value) : EvalM Unit := do
  let some value := (← EvalM.get).objects.lookup location.root | fault .danglingRoot
  let value ← writeValuePath fuel module value location.path replacement
  bindRoot location.root value

def expectInt : Value → EvalM (IntTy × Int)
  | .int ty value => pure (ty, value)
  | _ => fault .shape

def expectBool : Value → EvalM Bool
  | .bool value => pure value
  | _ => fault .shape

def expectRef : Value → EvalM Loc
  | .ref location => pure location
  | _ => fault .shape

def sameIntType (first second : IntTy) : EvalM Unit :=
  if first == second then pure () else fault .shape

def comparable : Value → Value → EvalM (Int × Int)
  | .int first a, .int second b => do sameIntType first second; pure (a, b)
  | .bool a, .bool b => pure (if a then 1 else 0, if b then 1 else 0)
  | _, _ => fault .shape

def renderValue : Value → EvalM ByteArray
  | .int _ value => pure (toString value).toUTF8
  | .bool true => pure "true".toUTF8
  | .bool false => pure "false".toUTF8
  | _ => fault .shape

def freshAct : EvalM ActId := do
  let state ← EvalM.get
  EvalM.set { state with nextAct := state.nextAct + 1 }
  pure state.nextAct

def freshScope : EvalM ScopeInst := do
  let state ← EvalM.get
  EvalM.set { state with nextScope := state.nextScope + 1 }
  pure state.nextScope

def rootOf (environment : RuntimeActivation) (localVar : VarId) : EvalM RootInst := do
  let some descriptor := environment.vars[localVar]? | fault .unbound
  let some (_, scopeInst) := environment.scopes.find? (fun entry => entry.1 == descriptor.scope) | fault .unbound
  pure (.local environment.act scopeInst localVar)

def selectTarget? (target : Core.NonlocalTarget) (activations : List RuntimeActivation) : Option RuntimeActivation :=
  activations.find? (fun activation => target.contains activation.implementation)

def releaseScopeState (environment : RuntimeActivation) (scope : Nat) (scopeInst : ScopeInst)
    (state : ExecutionState) : ExecutionState :=
  let roots := (environment.vars.toList.zipIdx).filterMap fun (localVar, index) =>
    if localVar.scope == scope then some (RootInst.local environment.act scopeInst index) else none
  { state with
    objects := state.objects.filter (fun entry => !roots.contains entry.1)
    objectOrdinals := state.objectOrdinals.filter (fun entry => !roots.contains entry.1)
    activations := state.activations.map (fun current => if current.act == environment.act then { current with scopes := environment.scopes } else current) }

def releaseScope (environment : RuntimeActivation) (scope : Nat) (scopeInst : ScopeInst) : EvalM Unit := do
  EvalM.set (releaseScopeState environment scope scopeInst (← EvalM.get))

def bindAll (act : ActId) (scopeInst : ScopeInst) (values : List (VarId × Value)) : EvalM Unit := do
  for (localVar, value) in values do bindRoot (.local act scopeInst localVar) value

def emitStdout (bytes : ByteArray) : EvalM Unit := liftConstruction 0 (appendStdout bytes)

def newDestination (module : LayoutEnv) (owner : ActId) (ty : Ty) (request : Core.ConstructionRequest)
    (origin : OriginId) (storage : Option StorageId := none) (knownCount : Option Nat := none) : EvalM DestinationId := do
  let storage ← match storage with
    | some storage => pure storage
    | none => liftConstruction origin reserveStorage
  let capability : Core.Destination Ty := ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩
  liftConstruction origin (openDestination storage capability (← receivingLayout module ty) knownCount)

def channelsFor (module : LayoutEnv) (owner : ActId) (results : List ResultDescriptor) (origin : OriginId) : EvalM (List Channel) := do
  results.mapM fun descriptor => match descriptor.request with
    | .register => pure (.register descriptor.ty)
    | .value => do pure (.construct (← newDestination module owner descriptor.ty .value origin))
    | .elementRun => do pure (.construct (← newDestination module owner descriptor.ty .elementRun origin))

def completedDestination (id : DestinationId) : EvalM DestinationId := do
  let destination ← getDestination id
  match destination.progress with
  | .built _ | .published _ | .attached _ => pure id
  | _ =>
      let state ← EvalM.get
      let some replacement := state.construction.destinations.toList.reverse.find? (fun current =>
        current.backing.receiverStorage == destination.backing.receiverStorage &&
        current.capability.start == destination.capability.start &&
        current.capability.owner == destination.capability.owner &&
        (match current.progress with | .built _ | .published _ | .attached _ => true | _ => false)) | fault .flow
      pure replacement.capability.id

def carrierValue : Carrier → EvalM Value
  | .register value => pure value
  | .completed destination => do pure (.stored (← storedDestination destination))

def singleCarrier (carriers : List Carrier) : EvalM Carrier :=
  match carriers with
  | [carrier] => pure carrier
  | [] => pure (.register .unit)
  | _ => fault .arity

def publishCarriers (origin : OriginId) (carriers : List Carrier) : EvalM Unit :=
  liftConstruction origin (publishOperation (carriers.filterMap fun carrier => match carrier with
    | .completed destination => some destination
    | .register _ => none))

structure RuntimeView where
  location : Loc
  start : Nat
  count : Nat
  dynamic : Bool

def arrayLength (value : Value) : EvalM (Nat × Bool) := do
  match value with
  | .fixed elements => pure (elements.size, false)
  | .stored stored =>
      let (_, run) ← sampledStored stored
      let dynamic := match stored.ty with
        | .grow _ | .growshrink _ => true
        | _ => false
      pure (run.count, dynamic)
  | _ => fault .shape

def readRun (fuel : Nat) (module : LayoutEnv) (view : RuntimeView) : EvalM (List Value) :=
  (List.range view.count).mapM fun index =>
    readLoc fuel module ⟨view.location.root, view.location.path ++ [view.start + index]⟩

def activeProgress : DestinationProgress → Bool
  | .open _ | .suspended _ _ | .built _ | .exiting _ _ => true
  | _ => false

def descendsFrom (state : ConstructionState) (id ancestor : DestinationId) : Bool := Id.run do
  let mut current := id
  for _ in [0:state.destinations.size + 1] do
    if current == ancestor then return true
    let some destination := state.destinations[current]? | return false
    match destination.use with
    | .receiver => return false
    | .child parent | .replacement parent => current := parent
  return false

def cleanupDestination (origin : OriginId) (id : DestinationId) (carriers : List Carrier) : EvalM Unit := do
  let destination ← getDestination id
  if !activeProgress destination.progress then pure ()
  else
    let state ← EvalM.get
    let preserved := carriers.findSome? fun carrier => match carrier with
      | .completed replacementId => do
          let replacement ← state.construction.destinations[replacementId]?
          match replacement.use with
          | .replacement superseded =>
              if descendsFrom state.construction id superseded then some replacementId else none
          | _ => none
      | _ => none
    match preserved with
    | some replacement => liftConstruction origin (abandonPreservingExit id replacement)
    | none =>
        if carriers.any (fun carrier => match carrier with
          | .completed destination => destination == id
          | _ => false) then pure ()
        else liftConstruction origin (abandonTree id)

def mapStepState (change : ExecutionState → ExecutionState) : ExecutionStep α → ExecutionStep α
  | .ok value state => .ok value (change state)
  | .stop reason state => .stop reason (change state)
  | .escape target carriers state => .escape target carriers (change state)
  | .jump target kind state => .jump target kind (change state)

def protectDestination (origin : OriginId) (id : DestinationId) (action : EvalM α) : EvalM α := fun state =>
  let cleanup := fun (carriers : List Carrier) (result : ExecutionState → ExecutionStep α) (state' : ExecutionState) =>
    match cleanupDestination origin id carriers state' with
    | .ok () state'' => result state''
    | .stop reason state'' => ExecutionStep.stop reason state''
    | .escape target carriers state'' => ExecutionStep.escape target carriers state''
    | .jump target kind state'' => ExecutionStep.jump target kind state''
  match action state with
  | .escape target carriers state' => cleanup carriers (.escape target carriers) state'
  | .jump target kind state' =>
      let carriers := match kind with | .breakValue carriers => carriers | .continueLoop => []
      cleanup carriers (.jump target kind) state'
  | result => result

def withScope (environment : RuntimeActivation) (scope scopeInst : Nat) (action : EvalM α) : EvalM α := fun state =>
  let cleanup := fun (result : ExecutionState → ExecutionStep α) (state' : ExecutionState) =>
    match releaseScope environment scope scopeInst state' with
    | .ok () state'' => result state''
    | .stop reason state'' => ExecutionStep.stop reason state''
    | .escape target carriers state'' => ExecutionStep.escape target carriers state''
    | .jump target kind state'' => ExecutionStep.jump target kind state''
  match action state with
  | .ok value state' => cleanup (.ok value) state'
  | .escape target carriers state' => cleanup (.escape target carriers) state'
  | .jump target kind state' => cleanup (.jump target kind) state'
  | .stop reason state' => .stop reason state'

def withBreakTarget (act : ActId) (scope : BreakScope) (channels : List Channel) (action : EvalM α)
    (receive : JumpKind → EvalM α) : EvalM α := fun state =>
  let id := state.nextScope
  let target : BreakTarget := ⟨id, act, scope, channels⟩
  let state := { state with nextScope := id + 1, breaks := target :: state.breaks }
  let result := mapStepState (fun current => { current with breaks := current.breaks.filter (fun entry => entry.id != id) }) (action state)
  match result with
  | .jump actual kind state' =>
      if actual == id then receive kind state' else .jump actual kind state'
  | result => result

def jump (target : Nat) (kind : JumpKind) : EvalM α := fun state => .jump target kind state

def currentBreak (act : ActId) (scope : Option BreakScope := none) : EvalM BreakTarget := do
  let some target := (← EvalM.get).breaks.find? (fun target => target.act == act && (scope.isNone || scope == some target.scope)) | fault .flow
  pure target

def landCarriers (origin : OriginId) (carriers : List Carrier) : EvalM Unit := do
  for carrier in carriers do
    match carrier with
    | .register _ => pure ()
    | .completed id =>
        let destination ← getDestination id
        match destination.use with
        | .replacement _ => liftConstruction origin (landExitReplacement id)
        | _ => pure ()

def finishChannels (layout : LayoutEnv) (resultTypes : List Ty)
    (carriers : List Carrier) (origin : OriginId) : EvalM Unit := do
  landCarriers origin carriers
  if carriers.length != resultTypes.length then fault .arity
  for (carrier, result) in carriers.zip resultTypes do
    match carrier with
    | .register _ => pure ()
    | .completed id =>
        let destination ← getDestination id
        let receivingPacked := match destination.capability.layout with | .varr _ => true | _ => false
        if destination.layout == .packed && destination.capability.request == .value && !receivingPacked then
          liftConstruction origin (removeConstructionHeader id)
          liftConstruction origin (restoreReceivingLayout id (← receivingLayout layout destination.capability.layout))
        liftConstruction origin (adaptDestinationType id result)

def finishActivation (layout : LayoutEnv) (activation : RuntimeActivation) (resultTypes : List Ty)
    (origin : OriginId) (action : EvalM (List Carrier)) : EvalM (List Carrier) := fun state =>
  let finish := fun carriers state' =>
    let state' := { state' with activations := state'.activations.filter (fun current => current.act != activation.act) }
    match finishChannels layout resultTypes carriers origin state' with
    | .ok () state'' => ExecutionStep.ok carriers state''
    | .stop reason state'' => ExecutionStep.stop reason state''
    | .escape target escaped state'' => ExecutionStep.escape target escaped state''
    | .jump target kind state'' => ExecutionStep.jump target kind state''
  match action state with
  | .ok carriers state' => finish carriers state'
  | .escape target carriers state' =>
      if target == activation.act then finish carriers state'
      else .escape target carriers { state' with activations := state'.activations.filter (fun current => current.act != activation.act) }
  | .stop reason state' => .stop reason state'
  | .jump _ _ state' => .stop (.fault .flow) state'

def joinBytes (separator : ByteArray) : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | first :: rest => rest.foldl (fun bytes part => bytes ++ separator ++ part) first

def quoteBytes (bytes : ByteArray) : ByteArray := Id.run do
  let mut result := "\"".toUTF8
  for byte in bytes.data do
    result := result ++ match byte.toNat with
      | 34 => "\\\"".toUTF8
      | 92 => "\\\\".toUTF8
      | 10 => "\\n".toUTF8
      | 13 => "\\r".toUTF8
      | 9 => "\\t".toUTF8
      | _ => ⟨#[byte]⟩
  return result ++ "\"".toUTF8

def copyValue : Nat → LayoutEnv → DestinationId → Value → OriginId → Option Core.CopySource → EvalM Unit
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, destination, value, origin, source => do
      let pending ← getDestination destination
      let some element := elementType pending.capability.logicalType | fault .shape
      match value with
      | .stored stored =>
          let (bytes, run) ← sampledStored stored
          if run.element != element then fault .shape
          liftConstruction origin (recordCopy (.storage (stored.object.getD stored.storage) stored.path) destination)
          for index in [0:run.count] do
            let (start, finish) ← liftLayout (elementInterval fuel config bytes run index)
            liftConstruction origin (writeElement destination (bytes.extract start finish))
      | .slice location start count =>
          let backing ← readLoc fuel config location
          let some source := source | fault .unbound
          match backing with
          | .stored stored =>
              let (bytes, run) ← storedPathRun stored
              if run.element != element then fault .shape
              if start + count > run.count then fault .pathRange
              liftConstruction origin (recordCopy source destination)
              for index in [0:count] do
                let (start, finish) ← liftLayout (elementInterval fuel config bytes run (start + index))
                liftConstruction origin (writeElement destination (bytes.extract start finish))
          | .fixed values =>
              if start + count > values.size then fault .pathRange
              liftConstruction origin (recordCopy source destination)
              for value in values.extract start (start + count) do
                liftConstruction origin (writeElement destination (← liftExcept (fixedBytes fuel config element value)))
          | _ => fault .shape
      | .fixed values =>
          if let some source := source then liftConstruction origin (recordCopy source destination)
          for value in values do
            liftConstruction origin (writeElement destination (← liftExcept (fixedBytes fuel config element value)))
      | _ => fault .shape
      liftConstruction origin (finishDestination destination)

def deliverCarriers (fuel : Nat) (layout : LayoutEnv) (channels : List Channel)
    (carriers : List Carrier) (origin : OriginId) : EvalM (List Carrier) := do
  if channels.length != carriers.length then fault .arity
  (channels.zip carriers).mapM fun (channel, carrier) => do
    match channel, carrier with
    | .register _, .register value => pure (.register value)
    | .construct _, .completed destination => pure (.completed destination)
    | .construct destination, .register value =>
        copyValue fuel layout destination value origin none
        pure (.completed destination)
    | .register _, .completed _ => fault .shape

def repeatElement : Nat → LayoutEnv → DestinationId → Ty → DestinationId → OriginId → EvalM Unit
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, parent, element, source, origin => do
      let stored ← storedDestination source
      let storage ← getStorage stored.storage
      let finish ← liftLayout (packedEnd fuel config element storage.bytes stored.start)
      liftConstruction origin (recordCopy (.repeat source) parent)
      liftConstruction origin (writeElement parent (storage.bytes.extract stored.start finish))

def ownerDestination (module : LayoutEnv) (stored : StoredValue) (request : Core.ConstructionRequest)
    (knownCount : Option Nat) (origin : OriginId) : EvalM DestinationId := do
  match stored.destination with
  | some id =>
      let pending ← getDestination id
      match pending.progress with
      | .built _ => liftConstruction origin (openExtension id request knownCount)
      | .published _ => newDestination module pending.capability.owner stored.ty request origin (some stored.storage) knownCount
      | _ => fault .flow
  | none => newDestination module 0 stored.ty request origin (some stored.storage) knownCount

def publishOwner : Nat → LayoutEnv → Loc → StoredValue → DestinationId → OriginId → EvalM Unit
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, location, stored, destination, origin => do
      let pending ← getDestination destination
      match pending.use with
      | .child parent =>
          liftConstruction origin (attachExtension parent destination)
          let value ← storedDestination parent
          writeLoc fuel config location (.stored { value with ty := stored.ty, object := stored.object, writtenCount := max stored.writtenCount value.count })
      | .receiver =>
          publishCarriers origin [.completed destination]
          let storage ← getStorage stored.storage
          writeLoc fuel config location (.stored { stored with count := storage.publishedCount, destination := some destination, writtenCount := max stored.writtenCount storage.publishedCount })
      | .replacement _ => fault .flow

def openElementReceiving (module : LayoutEnv) (owner : ActId) (location : Loc)
    (stored : StoredValue) (element : Ty) (knownCount : Option Nat)
    (origin : OriginId) : EvalM DestinationId := do
  let (_, run) ← sampledStored stored
  let receiver : Loc := ⟨location.root, location.path ++ [run.count]⟩
  let layout ← receivingLayout module element
  match stored.destination with
  | some id =>
      let pending ← getDestination id
      match pending.progress with
      | .built _ => liftConstruction origin (openElementExtension id element layout knownCount receiver)
      | .published _ =>
          let capability : Core.Destination Ty := ⟨0, receiver, element, element, .value, 0, owner⟩
          liftConstruction origin (openDestination stored.storage capability layout knownCount)
      | _ => fault .flow
  | none =>
      let capability : Core.Destination Ty := ⟨0, receiver, element, element, .value, 0, owner⟩
      liftConstruction origin (openDestination stored.storage capability layout knownCount)

def publishElementReceiving : Nat → LayoutEnv → Loc → StoredValue → DestinationId → OriginId → EvalM Unit
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, location, stored, destination, origin => do
      let pending ← getDestination destination
      match pending.use with
      | .child parent =>
          liftConstruction origin (attachElementExtension parent destination)
          let value ← storedDestination parent
          writeLoc fuel config location (.stored { value with ty := stored.ty, object := stored.object, path := stored.path, writtenCount := max stored.writtenCount value.count })
      | .receiver =>
          liftConstruction origin (publishElementDestination destination)
          let storage ← getStorage stored.storage
          writeLoc fuel config location (.stored { stored with count := storage.publishedCount, writtenCount := max stored.writtenCount storage.publishedCount })
      | .replacement _ => fault .flow

def truncateOwner : Nat → LayoutEnv → Loc → Nat → OriginId → EvalM Unit
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, location, count, origin => do
      let .stored stored ← readLoc fuel config location | fault .shape
      let (bytes, run) ← sampledStored stored
      if count > run.count then fault .pathRange
      let finish ← liftLayout (elementsEnd fuel config run.element count bytes run.byteStart)
      let owner ← match stored.destination with
        | some id => do
            let destination ← getDestination id
            pure (match destination.progress with | .published _ => none | _ => some id)
        | none => pure none
      liftConstruction origin (truncateConstructionStorage stored.storage stored.start finish count owner (match stored.ty with | .limited _ _ => true | _ => false))
      writeLoc fuel config location (.stored { stored with count := count })

def appendFixedValues : Nat → LayoutEnv → Loc → List Value → OriginId → EvalM Unit
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, location, values, origin => do
      let .stored stored ← readLoc fuel config location | fault .shape
      let some element := elementType stored.ty | fault .shape
      let parts ← values.mapM (fun value => liftExcept (fixedBytes fuel config element value))
      let destination ← ownerDestination config stored .elementRun (some values.length) origin
      for bytes in parts do liftConstruction origin (writeElement destination bytes)
      liftConstruction origin (finishDestination destination)
      publishOwner fuel config location stored (← completedDestination destination) origin

def appendRun : Nat → LayoutEnv → Loc → RuntimeView → OriginId → EvalM Unit
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, location, view, origin => do
      let .stored stored ← readLoc fuel config location | fault .shape
      let source ← readLoc fuel config view.location
      let destination ← ownerDestination config stored .elementRun (some view.count) origin
      match source with
      | .stored source =>
          let (bytes, run) ← sampledStored source
          liftConstruction origin (recordCopy (.storage (source.object.getD source.storage) source.path) destination)
          for index in [0:view.count] do
            let (start, finish) ← liftLayout (elementInterval fuel config bytes run (view.start + index))
            liftConstruction origin (writeElement destination (bytes.extract start finish))
      | .fixed values =>
          let some element := elementType stored.ty | fault .shape
          for index in [0:view.count] do
            let some value := values[view.start + index]? | fault .pathRange
            liftConstruction origin (writeElement destination (← liftExcept (fixedBytes fuel config element value)))
      | _ => fault .shape
      liftConstruction origin (finishDestination destination)
      publishOwner fuel config location stored (← completedDestination destination) origin

inductive RenderPosition
  | topLevel
  | aggregatePart
  deriving DecidableEq

mutual

def renderAny : Nat → LayoutEnv → RenderPosition → Value → EvalM ByteArray
  | 0, _, _, _ => timeout
  | fuel + 1, config, nested, value => do
      match value with
      | .int _ _ | .bool _ => renderValue value
      | .unit => pure "()".toUTF8
      | .ref location => renderAny fuel config nested (← readLoc fuel config location)
      | .slice location start count => renderView fuel config nested ⟨location, start, count, false⟩
      | .stored stored => renderStored fuel config nested stored
      | .fixed values =>
          if values.all (fun value => match value with | .int .u8 _ => true | _ => false) then
            let bytes ← values.toList.mapM fun value => do
              let (_, byte) ← expectInt value
              pure (UInt8.ofNat byte.toNat)
            pure (if nested == .aggregatePart then quoteBytes ⟨bytes.toArray⟩ else ⟨bytes.toArray⟩)
          else renderElements fuel config values.toList
      | .record id fields =>
          let some descriptor := config.structs[id]? | fault .unbound
          if fields.size != descriptor.fields.size || descriptor.displayName.isEmpty then fault .shape
          let parts ← fields.toList.mapM (renderAny fuel config .aggregatePart)
          pure (descriptor.displayName.toUTF8 ++ " { ".toUTF8 ++ joinBytes ", ".toUTF8 parts ++ " }".toUTF8)

def renderElements : Nat → LayoutEnv → List Value → EvalM ByteArray
  | 0, _, _ => timeout
  | fuel + 1, config, values => do
      let parts ← values.mapM (renderAny fuel config .aggregatePart)
      pure ("[".toUTF8 ++ joinBytes ", ".toUTF8 parts ++ "]".toUTF8)

def renderStored : Nat → LayoutEnv → RenderPosition → StoredValue → EvalM ByteArray
  | 0, _, _, _ => timeout
  | fuel + 1, config, nested, stored => do
      let (bytes, run) ← sampledStored stored
      if run.element == .int .u8 then
        let (start, finish) ← liftLayout (sampledInterval fuel config bytes run)
        let bytes := bytes.extract start finish
        pure (if nested == .aggregatePart then quoteBytes bytes else bytes)
      else
        let values ← (List.range run.count).mapM (readStoredElement fuel config stored)
        renderElements fuel config values

def renderView : Nat → LayoutEnv → RenderPosition → RuntimeView → EvalM ByteArray
  | 0, _, _, _ => timeout
  | fuel + 1, config, nested, view => do
      let value ← readLoc fuel config view.location
      let rawBytes ← match value with
        | .stored stored => do pure ((← sampledStored stored).2.element == .int .u8)
        | .fixed values => pure (values.all (fun value => match value with | .int .u8 _ => true | _ => false))
        | _ => fault .shape
      let values ← readRun fuel config view
      if rawBytes then
        let bytes ← values.mapM fun value => do
          let (ty, byte) ← expectInt value
          if ty != .u8 then fault .shape
          pure (UInt8.ofNat byte.toNat)
        let bytes : ByteArray := ⟨bytes.toArray⟩
        pure (if nested == .aggregatePart then quoteBytes bytes else bytes)
      else renderElements fuel config values

end

end Goose.Construct
