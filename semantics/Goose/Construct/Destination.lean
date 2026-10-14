import Goose.Construct.Typing

namespace Goose.Construct
open Goose.Core

inductive ReceivingLayout
  | packed
  | elements
  | fixed (count : Nat)
  | limited (capacity slotBytes : Nat)
  deriving DecidableEq, Repr

structure ReceivingStorage where
  bytes : ByteArray
  publishedCount : Nat

inductive DestinationProgress
  | open (count : Nat)
  | suspended (count : Nat) (child : DestinationId)
  | built (count : Nat)
  | exiting (count : Nat) (replacement : DestinationId)
  | published (count : Nat)
  | attached (count : Nat)
  | abandoned
  | cancelled
  | retired
  deriving DecidableEq, Repr

inductive DestinationUse
  | receiver
  | child (parent : DestinationId)
  | replacement (superseded : DestinationId)
  deriving DecidableEq, Repr

inductive DestinationBacking
  | direct (storage : StorageId)
  | staged (receiver storage : StorageId)
  deriving DecidableEq, Repr

def DestinationBacking.writeStorage : DestinationBacking → StorageId
  | .direct storage | .staged _ storage => storage

def DestinationBacking.receiverStorage : DestinationBacking → StorageId
  | .direct storage | .staged storage _ => storage

structure ReceivingAdaptation where
  logicalType : Ty
  request : ConstructionRequest
  layout : ReceivingLayout
  start : Nat
  deriving Repr

structure PendingDestination where
  capability : Core.Destination Ty
  backing : DestinationBacking
  layout : ReceivingLayout
  use : DestinationUse
  progress : DestinationProgress
  writeEnd : Nat
  rollbackEnd : Nat
  knownCount : Option Nat
  adaptation : Option ReceivingAdaptation := none
  deriving Repr

def PendingDestination.storage (destination : PendingDestination) : StorageId :=
  destination.backing.writeStorage

structure ConstructionState where
  storage : Array ReceivingStorage
  destinations : Array PendingDestination
  events : List ConstructionEvent
  stdout : ByteArray

def ConstructionState.initial : ConstructionState := ⟨#[], #[], [], ByteArray.empty⟩

inductive ConstructionFault
  | storage
  | destination
  | ownership
  | protocol
  | capacity
  deriving DecidableEq, Repr

inductive ConstructionResult (α : Type)
  | ok (value : α) (state : ConstructionState)
  | fault (kind : ConstructionFault) (state : ConstructionState)

def ConstructionResult.finalState : ConstructionResult α → ConstructionState
  | .ok _ state | .fault _ state => state

abbrev ConstructionM (α : Type) := ConstructionState → ConstructionResult α

namespace ConstructionM
instance : Monad ConstructionM where
  pure value state := .ok value state
  bind action next state :=
    match action state with
    | .ok value state' => next value state'
    | .fault kind state' => .fault kind state'

def fail (kind : ConstructionFault) : ConstructionM α := fun state => .fault kind state

def get : ConstructionM ConstructionState := fun state => .ok state state

def set (state : ConstructionState) : ConstructionM Unit := fun _ => .ok () state
end ConstructionM

private def lookupDestination (id : DestinationId) : ConstructionM PendingDestination := do
  match (← ConstructionM.get).destinations[id]? with
  | some destination => pure destination
  | none => ConstructionM.fail .destination

private def writableDestination (id : DestinationId) : ConstructionM PendingDestination := do
  let destination ← lookupDestination id
  let state ← ConstructionM.get
  let valid := Id.run do
    let mut current := id
    for _ in [0:state.destinations.size + 1] do
      let some owner := state.destinations[current]? | return false
      match owner.use with
      | .receiver => return true
      | .child parentId =>
          let some parent := state.destinations[parentId]? | return false
          match parent.progress with
          | .suspended _ expected =>
              if expected != current then return false
              current := parentId
          | _ => return false
      | .replacement supersededId =>
          let some superseded := state.destinations[supersededId]? | return false
          match superseded.progress with
          | .exiting _ expected =>
              if expected != current then return false
              current := supersededId
          | _ => return false
    return false
  if !valid then ConstructionM.fail .protocol
  pure destination

private def lookupStorage (id : StorageId) : ConstructionM ReceivingStorage := do
  match (← ConstructionM.get).storage[id]? with
  | some storage => pure storage
  | none => ConstructionM.fail .storage

private def replaceDestination (id : DestinationId) (destination : PendingDestination) :
    ConstructionM Unit := do
  let state ← ConstructionM.get
  if id < state.destinations.size then
    ConstructionM.set { state with destinations := state.destinations.set! id destination }
  else ConstructionM.fail .destination

private def replaceStorage (id : StorageId) (storage : ReceivingStorage) : ConstructionM Unit := do
  let state ← ConstructionM.get
  if id < state.storage.size then
    ConstructionM.set { state with storage := state.storage.set! id storage }
  else ConstructionM.fail .storage

private def emit (event : ConstructionEvent) : ConstructionM Unit := do
  let state ← ConstructionM.get
  ConstructionM.set { state with events := state.events ++ [event] }

def reserveStorage (bytes : ByteArray := ByteArray.empty) (publishedCount : Nat := 0) :
    ConstructionM StorageId := do
  let state ← ConstructionM.get
  let id := state.storage.size
  ConstructionM.set { state with storage := state.storage.push ⟨bytes, publishedCount⟩ }
  pure id

private def overwriteBytes (bytes : ByteArray) (start : Nat) (payload : ByteArray) : ByteArray :=
  bytes.extract 0 start ++ payload ++ bytes.extract (start + payload.size) bytes.size

private def lengthPrefix : ByteArray := ⟨#[0, 0, 0, 0]⟩

private def hasPrefix (layout : ReceivingLayout) (request : ConstructionRequest) : Bool :=
  layout == .packed && request == .value

private def available (layout : ReceivingLayout) (storage : ReceivingStorage) (count : Nat) : Bool :=
  match layout with
  | .limited capacity _ => storage.publishedCount + count ≤ capacity
  | .fixed expected => count ≤ expected
  | .packed => count < 2 ^ 32
  | .elements => true

private def writingAvailable (destination : PendingDestination) (storage : ReceivingStorage) (count : Nat) : Bool :=
  match destination.backing with
  | .direct _ => available destination.layout storage count &&
      match destination.adaptation with
      | some receiving => available receiving.layout storage count
      | none => true
  | .staged _ _ => true

private def active (destination : PendingDestination) : Bool :=
  match destination.progress with
  | .open _ | .suspended _ _ | .built _ | .exiting _ _ => true
  | .published _ | .attached _ | .abandoned | .cancelled | .retired => false

private inductive StagingPolicy
  | automatic
  | explicit
  deriving DecidableEq

private def openDestinationWith (policy : StagingPolicy) (storageId : StorageId) (capability : Core.Destination Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) : ConstructionM DestinationId := do
  let storage ← lookupStorage storageId
  let state ← ConstructionM.get
  if state.destinations.any (fun d => (d.storage == storageId || d.backing.receiverStorage == storageId) && active d) then
    ConstructionM.fail .ownership
  if let some count := knownCount then
    if !available layout storage count then ConstructionM.fail .capacity
  else
    pure ()
  let backing ← match policy, layout, knownCount with
    | .automatic, .limited _ _, none => do pure (.staged storageId (← reserveStorage))
    | _, _, _ => pure (DestinationBacking.direct storageId)
  let state ← ConstructionM.get
  let storage ← lookupStorage backing.writeStorage
  let id := state.destinations.size
  let start := match layout, backing with
    | .limited _ slotBytes, .direct _ => storage.publishedCount * slotBytes
    | _, _ => storage.bytes.size
  if start > storage.bytes.size then ConstructionM.fail .storage
  let capability := { capability with id := id, start := start }
  let writeEnd := start + if hasPrefix layout capability.request then 4 else 0
  let destination : PendingDestination := ⟨capability, backing, layout, .receiver, .open 0, writeEnd,
    (match layout with | .limited _ _ => storage.bytes.size | _ => start), knownCount, none⟩
  ConstructionM.set { state with destinations := state.destinations.push destination }
  if hasPrefix layout capability.request then
    replaceStorage backing.writeStorage { storage with bytes := storage.bytes ++ lengthPrefix }
  emit (.begin id)
  match backing with
  | .staged _ _ => emit (.stage id)
  | .direct _ => pure ()
  pure id

def openDestination (storageId : StorageId) (capability : Core.Destination Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) : ConstructionM DestinationId :=
  openDestinationWith .automatic storageId capability layout knownCount

def openDestinationDirect (storageId : StorageId) (capability : Core.Destination Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) : ConstructionM DestinationId :=
  openDestinationWith .explicit storageId capability layout knownCount

def stageDestination (id : DestinationId) : ConstructionM Unit := do
  let destination ← writableDestination id
  match destination.progress, destination.layout, destination.backing, destination.knownCount, destination.use with
  | .open 0, .limited _ _, .direct receiverId, none, .receiver =>
      let stageId ← reserveStorage
      replaceDestination id { destination with
        backing := .staged receiverId stageId
        capability := { destination.capability with start := 0 }
        writeEnd := 0
        rollbackEnd := 0 }
      emit (.stage id)
  | _, _, _, _, _ => ConstructionM.fail .protocol

def writeElement (id : DestinationId) (bytes : ByteArray) : ConstructionM Unit := do
  let destination ← writableDestination id
  match destination.progress with
  | .open count =>
      let storage ← lookupStorage destination.storage
      if !writingAvailable destination storage (count + 1) then ConstructionM.fail .capacity
      match (destination.adaptation.map (·.layout)).getD destination.layout, destination.backing with
      | .limited _ slotBytes, _ =>
          if bytes.size != slotBytes then ConstructionM.fail .protocol
      | _, _ => pure ()
      match destination.use with
      | .child parentId =>
          let parent ← lookupDestination parentId
          match parent.layout, parent.progress, parent.backing, destination.backing with
          | .limited capacity slotBytes, .suspended parentCount _, .direct _, .direct _ =>
              if destination.capability.request == .elementRun then
                if parentCount + count + 1 > capacity then ConstructionM.fail .capacity
                if bytes.size != slotBytes then ConstructionM.fail .protocol
              else
                if parentCount + 1 > capacity then ConstructionM.fail .capacity
          | _, _, _, _ => pure ()
      | _ => pure ()
      replaceStorage destination.storage { storage with
        bytes := overwriteBytes storage.bytes destination.writeEnd bytes }
      replaceDestination id { destination with
        progress := .open (count + 1)
        writeEnd := destination.writeEnd + bytes.size }
      emit (.write id count)
  | _ => ConstructionM.fail .protocol

def openChild (parentId : DestinationId) (logicalType : Ty) (layout : ReceivingLayout) :
    ConstructionM DestinationId := do
  let parent ← writableDestination parentId
  match parent.progress with
  | .open count =>
      let storage ← lookupStorage parent.storage
      if !writingAvailable parent storage (count + 1) then ConstructionM.fail .capacity
      let state ← ConstructionM.get
      let id := state.destinations.size
      let capability := { parent.capability with
        id := id, layout := logicalType, logicalType := logicalType,
        request := .value, start := parent.writeEnd }
      let child : PendingDestination := ⟨capability, .direct parent.storage, layout, .child parentId, .open 0,
        capability.start + (if hasPrefix layout .value then 4 else 0),
        (match parent.layout with | .limited _ _ => storage.bytes.size | _ => capability.start), none, none⟩
      ConstructionM.set { state with destinations := state.destinations.push child }
      replaceDestination parentId { parent with progress := .suspended count id }
      if hasPrefix layout .value then
        replaceStorage parent.storage { storage with bytes := overwriteBytes storage.bytes capability.start lengthPrefix }
      emit (.begin id)
      pure id
  | _ => ConstructionM.fail .protocol

private def patchCount (bytes : ByteArray) (start count : Nat) : ByteArray := Id.run do
  let mut result := bytes
  for offset in [0:4] do
    result := result.set! (start + offset) (UInt8.ofNat (count / 2 ^ (offset * 8) % 256))
  return result

def finishDestination (id : DestinationId) : ConstructionM Unit := do
  let destination ← writableDestination id
  match destination.progress with
  | .open count =>
      match destination.layout with
      | .fixed expected =>
          if count != expected then ConstructionM.fail .protocol
      | _ => pure ()
      if hasPrefix destination.layout destination.capability.request then
        let storage ← lookupStorage destination.storage
        replaceStorage destination.storage
          { storage with bytes := patchCount storage.bytes destination.capability.start count }
      replaceDestination id { destination with progress := .built count }
  | _ => ConstructionM.fail .protocol

def attachChild (parentId childId : DestinationId) : ConstructionM Unit := do
  let parent ← writableDestination parentId
  let child ← writableDestination childId
  match parent.progress, child.progress, child.use with
  | .suspended count expected, .built childCount, .child owner =>
      if child.adaptation.isSome then ConstructionM.fail .protocol
      if expected != childId || owner != parentId || child.storage != parent.storage then
        ConstructionM.fail .ownership
      replaceDestination childId { child with progress := .attached childCount }
      replaceDestination parentId { parent with progress := .open (count + 1), writeEnd := child.writeEnd }
      emit (.write parentId count)
  | _, _, _ => ConstructionM.fail .protocol

private def publicationCheck (state : ConstructionState) (id : DestinationId) : Except ConstructionFault Unit := do
  let some destination := state.destinations[id]? | throw .destination
  match destination.progress, destination.use with
  | .built count, .receiver =>
      if destination.adaptation.isSome then throw .protocol
      let some receiver := state.storage[destination.backing.receiverStorage]? | throw .storage
      if !available destination.layout receiver count then throw .capacity
      if (state.storage[destination.storage]?).isNone then throw .storage
  | _, _ => throw .protocol

def preflightPublication (state : ConstructionState) (ids : List DestinationId) :
    Except ConstructionFault Unit := do
  if ids.eraseDups != ids then throw .ownership
  for id in ids do publicationCheck state id

def fitStagedDestination (id : DestinationId) : ConstructionM Unit := do
  let destination ← writableDestination id
  let count ← match destination.progress with
    | .built count => pure count
    | _ => ConstructionM.fail .protocol
  let (receiverId, stageId) ← match destination.backing with
    | .staged receiverId stageId => pure (receiverId,stageId)
    | _ => ConstructionM.fail .protocol
  let receiver ← lookupStorage receiverId
  let stage ← lookupStorage stageId
  let start ← match destination.use with
    | .receiver => do
        match destination.layout with
        | .limited _ slotBytes =>
            if !available destination.layout receiver count then ConstructionM.fail .capacity
            if stage.bytes.size != count * slotBytes then ConstructionM.fail .protocol
            pure (receiver.publishedCount * slotBytes)
        | _ => ConstructionM.fail .protocol
    | .child parentId => do
        let parent ← writableDestination parentId
        match parent.progress, parent.layout with
        | .suspended parentCount expected, .limited capacity slotBytes =>
            if expected != id || receiverId != parent.storage then ConstructionM.fail .ownership
            if parentCount + count > capacity then ConstructionM.fail .capacity
            if stage.bytes.size != count * slotBytes then ConstructionM.fail .protocol
            pure parent.writeEnd
        | _, _ => ConstructionM.fail .protocol
    | .replacement _ => ConstructionM.fail .protocol
  replaceStorage receiverId { receiver with bytes := overwriteBytes receiver.bytes start stage.bytes }
  replaceStorage stageId ⟨ByteArray.empty,0⟩
  replaceDestination id { destination with
    backing := .direct receiverId
    capability := { destination.capability with start := start }
    writeEnd := start + stage.bytes.size
    rollbackEnd := receiver.bytes.size }
  emit (.copy (.storage stageId []) id)

private def publishReady (id : DestinationId) : ConstructionM Unit := do
  let destination ← lookupDestination id
  match destination.progress, destination.use with
  | .built count, .receiver =>
      let receiver ← lookupStorage destination.backing.receiverStorage
      let storage ← match destination.backing with
        | .direct _ => pure receiver
        | .staged _ stageId => do
            let stage ← lookupStorage stageId
            emit (.copy (.storage stageId []) id)
            let start := match destination.layout with
              | .limited _ slotBytes => receiver.publishedCount * slotBytes
              | _ => receiver.bytes.size
            pure { receiver with bytes := overwriteBytes receiver.bytes start stage.bytes }
      let publishedCount := match destination.layout with
        | .elements | .limited _ _ => storage.publishedCount + count
        | .packed | .fixed _ => count
      replaceStorage destination.backing.receiverStorage { storage with publishedCount := publishedCount }
      let publishedStart := match destination.backing, destination.layout with
        | .staged _ _, .limited _ slotBytes => receiver.publishedCount * slotBytes
        | .staged _ _, _ => receiver.bytes.size
        | .direct _, _ => destination.capability.start
      replaceDestination id { destination with
        progress := .published count
        writeEnd := publishedStart + (destination.writeEnd - destination.capability.start)
        backing := .direct destination.backing.receiverStorage
        capability := { destination.capability with start := publishedStart } }
      match destination.backing with
      | .direct _ => pure ()
      | .staged _ stageId => replaceStorage stageId ⟨ByteArray.empty, 0⟩
      emit (.publish id)
  | _, _ => ConstructionM.fail .protocol

def publishOperation (ids : List DestinationId) : ConstructionM Unit := do
  match preflightPublication (← ConstructionM.get) ids with
  | .error fault => ConstructionM.fail fault
  | .ok () => for id in ids do publishReady id

def abandonDestination (id : DestinationId) : ConstructionM Unit := do
  let destination ← writableDestination id
  match destination.progress with
  | .open _ | .built _ =>
      let storage ← lookupStorage destination.storage
      replaceStorage destination.storage
        { storage with bytes := storage.bytes.extract 0 destination.rollbackEnd }
      replaceDestination id { destination with progress := .abandoned }
      emit (.abandon id)
  | .suspended _ _ | .exiting _ _ => ConstructionM.fail .protocol
  | .published _ | .attached _ | .abandoned | .cancelled | .retired => ConstructionM.fail .protocol

private def descendantOf (destinations : Array PendingDestination) (ancestor : DestinationId)
    (id : DestinationId) : Bool := Id.run do
  let mut current := id
  for _ in [0:destinations.size] do
    if current == ancestor then return true
    let some destination := destinations[current]? | return false
    match destination.use with
    | .receiver => return false
    | .replacement parent | .child parent => current := parent
  return false

def abandonTree (id : DestinationId) : ConstructionM Unit := do
  let parent ← writableDestination id
  match parent.progress with
  | .open _ | .built _ | .suspended _ _ => pure ()
  | .exiting _ _ | .published _ | .attached _ | .abandoned | .cancelled | .retired => ConstructionM.fail .protocol
  let state ← ConstructionM.get
  let descendants := state.destinations.toList.reverse.filter fun destination =>
    descendantOf state.destinations id destination.capability.id && active destination
  for destination in descendants do
    match destination.progress with
    | .exiting _ _ => ConstructionM.fail .protocol
    | _ => pure ()
  for destination in descendants do
    let current ← writableDestination destination.capability.id
    match current.progress with
    | .suspended count _ =>
        replaceDestination current.capability.id { current with progress := .open count }
    | _ => pure ()
    abandonDestination destination.capability.id

def openExitReplacement (supersededId : DestinationId) : ConstructionM DestinationId := do
  let superseded ← writableDestination supersededId
  let count ← match superseded.progress with
    | .open count | .built count | .suspended count _ => pure count
    | .exiting _ _ | .published _ | .attached _ | .abandoned | .cancelled | .retired => ConstructionM.fail .protocol
  let storage ← lookupStorage superseded.storage
  let state ← ConstructionM.get
  let id := state.destinations.size
  let capability := { superseded.capability with id := id, start := storage.bytes.size }
  let replacement : PendingDestination :=
    ⟨capability, superseded.backing, superseded.layout, .replacement supersededId, .open 0,
      capability.start + (if hasPrefix superseded.layout superseded.capability.request then 4 else 0),
      capability.start, none, superseded.adaptation⟩
  ConstructionM.set { state with destinations := state.destinations.push replacement }
  replaceDestination supersededId { superseded with progress := .exiting count id }
  if hasPrefix superseded.layout superseded.capability.request then
    replaceStorage superseded.storage { storage with bytes := storage.bytes ++ lengthPrefix }
  emit (.begin id)
  pure id

def protectedExitDiscarded (state : ConstructionState) (id replacementId : DestinationId) :
    Except ConstructionFault (List PendingDestination) := do
  let some replacement := state.destinations[replacementId]? | throw .destination
  let supersededId ← match replacement.use, replacement.progress with
    | .replacement supersededId, .built _ => pure supersededId
    | _, _ => throw .protocol
  let some superseded := state.destinations[supersededId]? | throw .destination
  match superseded.progress with
  | .exiting _ expected => if expected != replacementId then throw .ownership
  | _ => throw .protocol
  let some destination := state.destinations[id]? | throw .destination
  if !active destination || destination.storage != replacement.storage ||
      destination.capability.start > replacement.capability.start ||
      !descendantOf state.destinations supersededId id || id == replacementId then
    throw .ownership
  pure (state.destinations.toList.reverse.filter fun destination =>
    destination.capability.id != replacementId &&
      descendantOf state.destinations id destination.capability.id && active destination)

private def protectedAbandonment : List PendingDestination → ConstructionM Unit
  | [] => pure ()
  | destination :: rest => fun state =>
      let id := destination.capability.id
      if id < state.destinations.size then
        protectedAbandonment rest { state with
          destinations := state.destinations.set! id { destination with progress := .abandoned }
          events := state.events ++ [.abandon id] }
      else .fault .destination state

private theorem protectedAbandonment_storage (discarded : List PendingDestination) (state : ConstructionState) :
    (protectedAbandonment discarded state).finalState.storage = state.storage := by
  induction discarded generalizing state with
  | nil => rfl
  | cons destination rest ih =>
      simp only [protectedAbandonment]
      split
      · exact ih _
      · rfl

private theorem protectedAbandonment_events (discarded : List PendingDestination) (state : ConstructionState) :
    ∃ suffix, (protectedAbandonment discarded state).finalState.events = state.events ++ suffix := by
  induction discarded generalizing state with
  | nil => exact ⟨[], by simp [protectedAbandonment, pure, ConstructionResult.finalState]⟩
  | cons destination rest ih =>
      simp only [protectedAbandonment]
      split
      · obtain ⟨suffix, prefixed⟩ := ih { state with
          destinations := state.destinations.set! destination.capability.id { destination with progress := .abandoned }
          events := state.events ++ [.abandon destination.capability.id] }
        exact ⟨.abandon destination.capability.id :: suffix, by simpa [List.append_assoc] using prefixed⟩
      · exact ⟨[], by simp [ConstructionResult.finalState]⟩

private theorem protectedAbandonment_stdout (discarded : List PendingDestination) (state : ConstructionState) :
    (protectedAbandonment discarded state).finalState.stdout = state.stdout := by
  induction discarded generalizing state with
  | nil => rfl
  | cons destination rest ih =>
      simp only [protectedAbandonment]
      split
      · exact ih _
      · rfl

def abandonPreservingExit (id replacementId : DestinationId) : ConstructionM Unit := do
  match protectedExitDiscarded (← ConstructionM.get) id replacementId with
  | .error fault => ConstructionM.fail fault
  | .ok discarded => protectedAbandonment discarded

theorem abandonPreservingExit_storage (state : ConstructionState) (id replacementId : DestinationId) :
    (abandonPreservingExit id replacementId state).finalState.storage = state.storage := by
  simp only [abandonPreservingExit, ConstructionM.get, bind]
  cases checked : protectedExitDiscarded state id replacementId with
  | error fault => rfl
  | ok discarded => exact protectedAbandonment_storage discarded state

theorem abandonPreservingExit_stdout (state : ConstructionState) (id replacementId : DestinationId) :
    (abandonPreservingExit id replacementId state).finalState.stdout = state.stdout := by
  simp only [abandonPreservingExit, ConstructionM.get, bind]
  cases checked : protectedExitDiscarded state id replacementId with
  | error fault => rfl
  | ok discarded => exact protectedAbandonment_stdout discarded state

theorem abandonPreservingExit_events (state : ConstructionState) (id replacementId : DestinationId) :
    ∃ suffix, (abandonPreservingExit id replacementId state).finalState.events = state.events ++ suffix := by
  simp only [abandonPreservingExit, ConstructionM.get, bind]
  cases checked : protectedExitDiscarded state id replacementId with
  | error fault => exact ⟨[], by simp [ConstructionM.fail, ConstructionResult.finalState]⟩
  | ok discarded => exact protectedAbandonment_events discarded state

def acknowledgeAbandonment (id : DestinationId) : ConstructionM Unit := do
  let destination ← lookupDestination id
  match destination.progress with
  | .abandoned => replaceDestination id { destination with progress := .cancelled }
  | _ => ConstructionM.fail .protocol

def landingBytes (bytes : ByteArray) (receivingStart payloadStart : Nat) : ByteArray :=
  bytes.extract 0 receivingStart ++ bytes.extract payloadStart bytes.size

def ReceivingStorage.landExit (storage : ReceivingStorage) (receivingStart payloadStart : Nat) : ReceivingStorage :=
  { storage with bytes := landingBytes storage.bytes receivingStart payloadStart }

def landReceivingStorage (storageId : StorageId) (receivingStart payloadStart : Nat) :
    ConstructionM Unit := fun state =>
  match state.storage[storageId]? with
  | none => .fault .storage state
  | some storage =>
      if receivingStart ≤ payloadStart && payloadStart ≤ storage.bytes.size then
        .ok () { state with
          storage := state.storage.set! storageId (storage.landExit receivingStart payloadStart) }
      else .fault .ownership state

private def landCompletedReplacement (replacementId supersededId : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) : ConstructionM Unit := do
  let _ ← lookupStorage replacement.storage
  if replacement.capability.start < superseded.capability.start then ConstructionM.fail .ownership
  let state ← ConstructionM.get
  let discarded := state.destinations.toList.reverse.filter fun destination =>
    destination.capability.id != replacementId &&
      descendantOf state.destinations supersededId destination.capability.id && active destination
  protectedAbandonment discarded
  landReceivingStorage replacement.storage superseded.capability.start replacement.capability.start
  replaceDestination replacementId { replacement with
    capability := { replacement.capability with start := superseded.capability.start }
    use := superseded.use
    progress := .built count
    writeEnd := replacement.writeEnd - (replacement.capability.start - superseded.capability.start)
    rollbackEnd := superseded.rollbackEnd }
  if let some (parentId, parent) := parentUpdate then
    replaceDestination parentId parent
  if superseded.capability.start < replacement.capability.start then
    emit (.relocate replacementId .exitValue)

def landExitReplacement (replacementId : DestinationId) : ConstructionM Unit := do
  let replacement ← lookupDestination replacementId
  let (supersededId, count) ← match replacement.use, replacement.progress with
    | .replacement old, .built count => pure (old, count)
    | _, _ => ConstructionM.fail .protocol
  let superseded ← lookupDestination supersededId
  match superseded.progress with
  | .exiting _ expected =>
      if expected != replacementId || superseded.storage != replacement.storage then
        ConstructionM.fail .ownership
  | .abandoned | .cancelled =>
      if superseded.storage != replacement.storage then ConstructionM.fail .ownership
  | _ => ConstructionM.fail .protocol
  let parentUpdate ← match superseded.use with
    | .receiver => pure none
    | .child parentId => do
        let parent ← lookupDestination parentId
        match parent.progress with
        | .suspended parentCount expected =>
            if expected != supersededId then ConstructionM.fail .ownership
            pure (some (parentId, { parent with progress := .suspended parentCount replacementId }))
        | _ => ConstructionM.fail .protocol
    | .replacement _ => ConstructionM.fail .protocol
  landCompletedReplacement replacementId supersededId count replacement superseded parentUpdate


def recordCopy (source : CopySource) (id : DestinationId) : ConstructionM Unit := do
  let destination ← writableDestination id
  match destination.progress with
  | .open _ =>
      match source with
      | .storage sourceId _ => let _ ← lookupStorage sourceId; pure ()
      | .repeat sourceId =>
          let sourceDestination ← lookupDestination sourceId
          match sourceDestination.progress with
          | .built _ | .attached _ | .published _ => pure ()
          | _ => ConstructionM.fail .protocol
      emit (.copy source id)
  | _ => ConstructionM.fail .protocol

def appendStdout (bytes : ByteArray) : ConstructionM Unit := do
  let state ← ConstructionM.get
  ConstructionM.set { state with stdout := state.stdout ++ bytes }

def openExtension (parentId : DestinationId) (request : ConstructionRequest)
    (knownCount : Option Nat) : ConstructionM DestinationId := do
  let parent ← writableDestination parentId
  let count ← match parent.progress with
    | .built count => pure count
    | _ => ConstructionM.fail .protocol
  let storage ← lookupStorage parent.storage
  if let some additional := knownCount then
    match parent.layout, parent.backing with
    | .limited capacity _, .direct _ =>
        if count + additional > capacity then ConstructionM.fail .capacity
    | .packed, _ =>
        if count + additional ≥ 2 ^ 32 then ConstructionM.fail .capacity
    | .fixed _, _ => ConstructionM.fail .protocol
    | _, _ => pure ()
  let backing ← match parent.layout, parent.backing, knownCount with
    | .limited _ _, .direct _, none => do
        pure (.staged parent.storage (← reserveStorage))
    | _, _, _ => pure (.direct parent.storage)
  let start := match backing with
    | .staged _ _ => 0
    | .direct _ => parent.writeEnd
  let state ← ConstructionM.get
  let id := state.destinations.size
  let capability := { parent.capability with id := id, request := request, start := start }
  let child : PendingDestination :=
    ⟨capability, backing, .elements, .child parentId, .open 0, start,
      (match backing, parent.layout with
      | .direct _, .limited _ _ => storage.bytes.size
      | _, _ => start), knownCount, none⟩
  ConstructionM.set { state with destinations := state.destinations.push child }
  replaceDestination parentId { parent with progress := .suspended count id }
  emit (.begin id)
  match backing with
  | .staged _ _ => emit (.stage id)
  | .direct _ => pure ()
  pure id

def attachExtension (parentId childId : DestinationId) : ConstructionM Unit := do
  let parent ← writableDestination parentId
  let child ← writableDestination childId
  match parent.progress, child.progress, child.use with
  | .suspended count expected, .built childCount, .child owner =>
      if child.adaptation.isSome then ConstructionM.fail .protocol
      if expected != childId || owner != parentId || child.backing.receiverStorage != parent.storage ||
          child.layout != .elements then ConstructionM.fail .ownership
      match parent.layout, parent.backing with
      | .limited capacity _, .direct _ =>
          if count + childCount > capacity then ConstructionM.fail .capacity
      | .packed, _ =>
          if count + childCount ≥ 2 ^ 32 then ConstructionM.fail .capacity
      | .fixed _, _ => ConstructionM.fail .protocol
      | _, _ => pure ()
      let storage ← lookupStorage parent.storage
      let (storage, child) ← match child.backing with
        | .direct _ => pure (storage, child)
        | .staged _ stageId => do
            let stage ← lookupStorage stageId
            emit (.copy (.storage stageId []) childId)
            replaceStorage stageId ⟨ByteArray.empty, 0⟩
            pure ({ storage with bytes := overwriteBytes storage.bytes parent.writeEnd stage.bytes },
              { child with
                backing := .direct parent.storage
                capability := { child.capability with start := parent.writeEnd }
                writeEnd := parent.writeEnd + stage.bytes.size })
      replaceStorage parent.storage storage
      if hasPrefix parent.layout parent.capability.request then
        replaceStorage parent.storage { storage with
          bytes := patchCount storage.bytes parent.capability.start (count + childCount) }
      replaceDestination childId { child with progress := .attached childCount }
      replaceDestination parentId { parent with progress := .built (count + childCount), writeEnd := child.writeEnd }
      emit (.publish childId)
  | _, _, _ => ConstructionM.fail .protocol


def openElementExtension (parentId : DestinationId) (logicalType : Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) (receiverLoc : Core.Loc) :
    ConstructionM DestinationId := do
  let parent ← writableDestination parentId
  let count ← match parent.progress with
    | .built count => pure count
    | _ => ConstructionM.fail .protocol
  if parent.capability.logicalType.element? != some logicalType then ConstructionM.fail .protocol
  match parent.layout, parent.backing with
  | .limited capacity _, .direct _ =>
      if count + 1 > capacity then ConstructionM.fail .capacity
  | .packed, _ => if count + 1 ≥ 2 ^ 32 then ConstructionM.fail .capacity
  | .fixed _, _ => ConstructionM.fail .protocol
  | _, _ => pure ()
  let storage ← lookupStorage parent.storage
  let state ← ConstructionM.get
  let id := state.destinations.size
  let capability := { parent.capability with
    id := id, receiver := receiverLoc
    layout := logicalType, logicalType := logicalType, request := .value, start := parent.writeEnd }
  let child : PendingDestination := ⟨capability, .direct parent.storage, layout, .child parentId,
    .open 0, parent.writeEnd + (if hasPrefix layout .value then 4 else 0),
    (match parent.layout with | .limited _ _ => storage.bytes.size | _ => parent.writeEnd), knownCount, none⟩
  ConstructionM.set { state with destinations := state.destinations.push child }
  replaceDestination parentId { parent with progress := .suspended count id }
  if hasPrefix layout .value then
    replaceStorage parent.storage { storage with bytes := overwriteBytes storage.bytes parent.writeEnd lengthPrefix }
  emit (.begin id)
  pure id

def attachElementExtension (parentId childId : DestinationId) : ConstructionM Unit := do
  let parent ← writableDestination parentId
  let child ← writableDestination childId
  match parent.progress, child.progress, child.use, child.backing with
  | .suspended count expected, .built childCount, .child owner, .direct storageId =>
      if child.adaptation.isSome then ConstructionM.fail .protocol
      if expected != childId || owner != parentId || storageId != parent.storage ||
          child.capability.request != .value ||
          parent.capability.logicalType.element? != some child.capability.logicalType then
        ConstructionM.fail .ownership
      let storage ← lookupStorage parent.storage
      match parent.layout with
      | .limited capacity slotBytes =>
          if count + 1 > capacity then ConstructionM.fail .capacity
          if child.writeEnd - child.capability.start != slotBytes then ConstructionM.fail .protocol
      | .packed => if count + 1 ≥ 2 ^ 32 then ConstructionM.fail .capacity
      | .fixed _ => ConstructionM.fail .protocol
      | .elements => pure ()
      if hasPrefix parent.layout parent.capability.request then
        replaceStorage parent.storage { storage with
          bytes := patchCount storage.bytes parent.capability.start (count + 1) }
      replaceDestination childId { child with progress := .attached childCount }
      replaceDestination parentId { parent with progress := .built (count + 1), writeEnd := child.writeEnd }
      emit (.publish childId)
  | _, _, _, _ => ConstructionM.fail .protocol

def publishElementDestination (id : DestinationId) : ConstructionM Unit := do
  let destination ← writableDestination id
  match destination.progress, destination.use, destination.backing with
  | .built count, .receiver, .direct storageId =>
      if destination.adaptation.isSome then ConstructionM.fail .protocol
      if destination.capability.request != .value then ConstructionM.fail .protocol
      let storage ← lookupStorage storageId
      replaceStorage storageId { storage with publishedCount := storage.publishedCount + 1 }
      replaceDestination id { destination with progress := .published count }
      emit (.publish id)
  | _, _, _ => ConstructionM.fail .protocol

def retireRepeatedSource (parentId sourceId : DestinationId) : ConstructionM Unit := do
  let parent ← writableDestination parentId
  let source ← writableDestination sourceId
  match parent.progress, source.progress, source.use, source.backing with
  | .open _, .built _, .receiver, .direct storageId =>
      if parentId == sourceId || parent.storage == storageId ||
          parent.backing.receiverStorage == storageId || source.capability.request != .value ||
          parent.capability.logicalType.element? != some source.capability.logicalType then
        ConstructionM.fail .ownership
      let storage ← lookupStorage storageId
      if storage.publishedCount != 0 || source.capability.start != 0 || source.rollbackEnd != 0 then
        ConstructionM.fail .ownership
      let state ← ConstructionM.get
      if state.destinations.any (fun destination =>
          destination.capability.id != sourceId && destination.storage == storageId && active destination) then
        ConstructionM.fail .ownership
      replaceStorage storageId ⟨ByteArray.empty, 0⟩
      replaceDestination sourceId { source with progress := .retired }
  | _, _, _, _ => ConstructionM.fail .protocol

def truncateConstructionStorage (storageId : StorageId) (start finish count : Nat)
    (owner : Option DestinationId) (retainSlots : Bool) : ConstructionM Unit := do
  let storage ← lookupStorage storageId
  if start > finish || finish > storage.bytes.size then ConstructionM.fail .storage
  let state ← ConstructionM.get
  let destination ← match owner with
    | some id => do
        let destination ← writableDestination id
        if destination.storage != storageId || destination.capability.start != start then
          ConstructionM.fail .ownership
        match destination.progress with
        | .built oldCount =>
            if count > oldCount then ConstructionM.fail .protocol
            pure (some destination)
        | _ => ConstructionM.fail .protocol
    | none => do
        if count > storage.publishedCount then ConstructionM.fail .protocol
        if state.destinations.any (fun d =>
            (d.storage == storageId || d.backing.receiverStorage == storageId) && active d) then
          ConstructionM.fail .ownership
        pure none
  let bytes := if retainSlots then storage.bytes else storage.bytes.extract 0 finish
  match destination with
  | some destination =>
      let bytes := if hasPrefix destination.layout destination.capability.request then
          patchCount bytes start count else bytes
      replaceStorage storageId { storage with bytes := bytes }
      replaceDestination destination.capability.id { destination with progress := .built count, writeEnd := finish }
  | none => replaceStorage storageId ⟨bytes, count⟩

def removeConstructionHeader (id : DestinationId) : ConstructionM Unit := do
  let destination ← writableDestination id
  match destination.progress with
  | .built _ =>
      if !hasPrefix destination.layout destination.capability.request then
        ConstructionM.fail .protocol
      let storage ← lookupStorage destination.storage
      let start := destination.capability.start
      if start + 4 > storage.bytes.size then ConstructionM.fail .storage
      replaceStorage destination.storage { storage with
        bytes := storage.bytes.extract 0 start ++ storage.bytes.extract (start + 4) storage.bytes.size }
      replaceDestination id { destination with layout := .elements, writeEnd := destination.writeEnd - 4 }
      emit (.relocate id .headerRemoval)
  | _ => ConstructionM.fail .protocol


def adaptDestinationType (id : DestinationId) (logicalType : Ty) : ConstructionM Unit := do
  let destination ← writableDestination id
  match destination.progress with
  | .open _ | .built _ => pure ()
  | _ => ConstructionM.fail .protocol
  if !logicalType.constructible ||
      !logicalType.adaptsTo destination.capability.logicalType then ConstructionM.fail .protocol
  replaceDestination id { destination with
    capability := { destination.capability with logicalType := logicalType } }

def prepareNamedBinding (id : DestinationId) (localType : Ty) : ConstructionM Unit := do
  let destination ← writableDestination id
  match destination.progress with
  | .open 0 => pure ()
  | _ => ConstructionM.fail .protocol
  if destination.capability.request != .value ||
      !localType.adaptsTo destination.capability.logicalType then ConstructionM.fail .protocol
  let storage ← lookupStorage destination.storage
  let needsPrefix : Bool := match localType with
    | .varr _ => destination.layout != .packed
    | _ => false
  if needsPrefix then
    if destination.writeEnd != destination.capability.start then ConstructionM.fail .protocol
    let start := destination.capability.start
    replaceStorage destination.storage { storage with
      bytes := storage.bytes.extract 0 start ++ lengthPrefix ++ storage.bytes.extract start storage.bytes.size }
  replaceDestination id { destination with
    capability := { destination.capability with logicalType := localType }
    layout := if needsPrefix then .packed else destination.layout
    writeEnd := destination.writeEnd + if needsPrefix then 4 else 0 }


def restoreReceivingLayout (id : DestinationId) (layout : ReceivingLayout) : ConstructionM Unit := do
  let destination ← writableDestination id
  let count ← match destination.progress with
    | .built count => pure count
    | _ => ConstructionM.fail .protocol
  let agrees : Bool := match destination.capability.layout, layout with
    | .grow _, .elements | .growshrink _, .elements => true
    | .varr _, .packed => destination.layout == .packed
    | .arr _ expected, .fixed actual => expected == actual && count == expected
    | .limited _ expected, .limited actual _ => expected == actual
    | _, _ => false
  if !agrees then ConstructionM.fail .protocol
  replaceDestination id { destination with layout := layout }


def adaptConstructionDestination (id : DestinationId) (producerType : Ty)
    (request : ConstructionRequest) : ConstructionM Unit := do
  let destination ← writableDestination id
  match destination.progress with
  | .open 0 => pure ()
  | _ => ConstructionM.fail .protocol
  if destination.adaptation.isSome || !producerType.storageType ||
      producerType.element?.isNone || !destination.capability.logicalType.storageType ||
      destination.capability.logicalType.element?.isNone ||
      !producerType.adaptsTo destination.capability.logicalType then ConstructionM.fail .protocol
  let receiving : ReceivingAdaptation :=
    ⟨destination.capability.logicalType,destination.capability.request,destination.layout,destination.capability.start⟩
  let receivingPrefix := hasPrefix receiving.layout receiving.request
  let producerPrefix : Bool := match producerType with
    | .varr _ => request == .value
    | _ => false
  if destination.writeEnd != destination.capability.start + (if receivingPrefix then 4 else 0) then
    ConstructionM.fail .protocol
  if producerPrefix && !receivingPrefix then
    let storage ← lookupStorage destination.storage
    if destination.capability.start > storage.bytes.size then ConstructionM.fail .storage
    replaceStorage destination.storage { storage with
      bytes := storage.bytes.extract 0 destination.capability.start ++ lengthPrefix ++
        storage.bytes.extract destination.capability.start storage.bytes.size }
  let layout := if producerPrefix then ReceivingLayout.packed else match receiving.layout with
    | .packed => .elements
    | layout => layout
  replaceDestination id { destination with
    capability := { destination.capability with
      logicalType := producerType
      request := request
      start := destination.capability.start + if receivingPrefix && !producerPrefix then 4 else 0 }
    layout := layout
    writeEnd := destination.writeEnd + if producerPrefix && !receivingPrefix then 4 else 0
    adaptation := some receiving }

def finishConstructionAdaptation (id : DestinationId) : ConstructionM Unit := do
  let destination ← lookupDestination id
  let some receiving := destination.adaptation | ConstructionM.fail .protocol
  let count ← match destination.progress with
    | .built count => do
        let _ ← writableDestination id
        let storage ← lookupStorage destination.storage
        match destination.backing with
        | .direct _ =>
            if !available receiving.layout storage count then ConstructionM.fail .capacity
        | .staged _ _ => pure ()
        pure (some count)
    | .abandoned | .cancelled => pure none
    | _ => ConstructionM.fail .protocol
  match count with
  | some count =>
      if hasPrefix destination.layout destination.capability.request &&
          !hasPrefix receiving.layout receiving.request then
        removeConstructionHeader id
      if hasPrefix receiving.layout receiving.request then
        let storage ← lookupStorage destination.storage
        if receiving.start + 4 > storage.bytes.size then ConstructionM.fail .storage
        replaceStorage destination.storage { storage with
          bytes := patchCount storage.bytes receiving.start count }
  | none => pure ()
  let current ← lookupDestination id
  replaceDestination id { current with
    capability := { current.capability with
      logicalType := receiving.logicalType
      request := receiving.request
      start := receiving.start }
    layout := receiving.layout
    adaptation := none }



def normalizeProducerDestination (id : DestinationId) (producerType : Ty) : ConstructionM Unit := do
  let destination ← writableDestination id
  let some receiving := destination.adaptation | ConstructionM.fail .protocol
  let count ← match destination.progress with
    | .built count => pure count
    | _ => ConstructionM.fail .protocol
  if !producerType.storageType || producerType.element?.isNone ||
      !producerType.adaptsTo destination.capability.logicalType then ConstructionM.fail .protocol
  let producerPrefix : Bool := match producerType with
    | .varr _ => destination.capability.request == .value
    | _ => false
  let producerStart := receiving.start +
    if hasPrefix receiving.layout receiving.request && !producerPrefix then 4 else 0
  if destination.capability.start != producerStart then ConstructionM.fail .protocol
  if producerPrefix then
    if !hasPrefix destination.layout destination.capability.request then ConstructionM.fail .protocol
    let storage ← lookupStorage destination.storage
    if producerStart + 4 > storage.bytes.size then ConstructionM.fail .storage
    replaceStorage destination.storage { storage with bytes := patchCount storage.bytes producerStart count }
  else if hasPrefix destination.layout destination.capability.request then
    removeConstructionHeader id
  let current ← lookupDestination id
  let layout := if producerPrefix then ReceivingLayout.packed else match receiving.layout with
    | .packed => .elements
    | layout => layout
  replaceDestination id { current with
    capability := { current.capability with logicalType := producerType, start := producerStart }
    layout := layout }



private abbrev KeepsOutput (action : ConstructionM α) : Prop :=
  ∀ state, (action state).finalState.stdout = state.stdout

private theorem keepsOutput_bind (action : ConstructionM α) (remaining : α → ConstructionM β)
    (first : KeepsOutput action) (next : ∀ value, KeepsOutput (remaining value)) :
    KeepsOutput (action >>= remaining) := by
  intro state
  have framed := first state
  cases result : action state with
  | ok value after =>
      simp only [bind,result]
      exact (next value after).trans (by simpa [result,ConstructionResult.finalState] using framed)
  | fault reason after => simpa [bind,result,ConstructionResult.finalState] using framed

private theorem keepsOutput_pure (value : α) : KeepsOutput (pure value) := fun _ => rfl
private theorem keepsOutput_fail (reason : ConstructionFault) : KeepsOutput (ConstructionM.fail (α := α) reason) := fun _ => rfl
private theorem keepsOutput_get : KeepsOutput ConstructionM.get := fun _ => rfl

private theorem keepsOutput_lookup_destination (id : DestinationId) : KeepsOutput (lookupDestination id) := by
  intro state
  simp only [lookupDestination,ConstructionM.get,bind]
  cases state.destinations[id]? <;> rfl

private theorem keepsOutput_lookup_storage (id : StorageId) : KeepsOutput (lookupStorage id) := by
  intro state
  simp only [lookupStorage,ConstructionM.get,bind]
  cases state.storage[id]? <;> rfl

private theorem keepsOutput_replace_destination (id : DestinationId) (destination : PendingDestination) :
    KeepsOutput (replaceDestination id destination) := by
  intro state
  simp only [replaceDestination,ConstructionM.get,bind]
  split <;> rfl

private theorem keepsOutput_replace_storage (id : StorageId) (storage : ReceivingStorage) :
    KeepsOutput (replaceStorage id storage) := by
  intro state
  simp only [replaceStorage,ConstructionM.get,bind]
  split <;> rfl

private theorem keepsOutput_emit (event : ConstructionEvent) : KeepsOutput (emit event) := fun _ => rfl

private theorem keepsOutput_writable_destination (id : DestinationId) : KeepsOutput (writableDestination id) := by
  apply keepsOutput_bind (lookupDestination id)
  · exact keepsOutput_lookup_destination id
  · intro destination
    apply keepsOutput_bind ConstructionM.get
    · exact keepsOutput_get
    · intro state
      intro current
      dsimp only
      split <;> rfl


private theorem keepsOutput_if (condition : Prop) [Decidable condition]
    (yes no : ConstructionM α) (first : KeepsOutput yes) (second : KeepsOutput no) :
    KeepsOutput (if condition then yes else no) := by
  by_cases selected : condition
  · simpa only [selected,↓reduceIte] using first
  · simpa only [selected,↓reduceIte] using second

theorem adaptDestinationType_stdout (id : DestinationId) (logicalType : Ty) (state : ConstructionState) :
    (adaptDestinationType id logicalType state).finalState.stdout = state.stdout := by
  apply keepsOutput_bind (writableDestination id)
  · exact keepsOutput_writable_destination id
  · intro destination
    cases destination.progress
    all_goals try exact fun _ => rfl
    all_goals
      apply keepsOutput_if
      · exact fun _ => rfl
      · exact keepsOutput_replace_destination _ _

theorem restoreReceivingLayout_stdout (id : DestinationId) (layout : ReceivingLayout) (state : ConstructionState) :
    (restoreReceivingLayout id layout state).finalState.stdout = state.stdout := by
  apply keepsOutput_bind (writableDestination id)
  · exact keepsOutput_writable_destination id
  · intro destination
    cases destination.progress
    all_goals try exact fun _ => rfl
    apply keepsOutput_if
    · exact fun _ => rfl
    · exact keepsOutput_replace_destination _ _

theorem removeConstructionHeader_stdout (id : DestinationId) (state : ConstructionState) :
    (removeConstructionHeader id state).finalState.stdout = state.stdout := by
  apply keepsOutput_bind (writableDestination id)
  · exact keepsOutput_writable_destination id
  · intro destination
    cases destination.progress
    all_goals try exact keepsOutput_fail .protocol
    apply keepsOutput_if
    · exact keepsOutput_fail .protocol
    · apply keepsOutput_bind (lookupStorage destination.storage)
      · exact keepsOutput_lookup_storage _
      · intro storage
        apply keepsOutput_if
        · exact keepsOutput_fail .storage
        · apply keepsOutput_bind (replaceStorage destination.storage _)
          · exact keepsOutput_replace_storage _ _
          · intro _
            apply keepsOutput_bind (replaceDestination id _)
            · exact keepsOutput_replace_destination _ _
            · intro _; exact keepsOutput_emit _



private theorem keepsOutput_land_receiving (storageId : StorageId) (receivingStart payloadStart : Nat) :
    KeepsOutput (landReceivingStorage storageId receivingStart payloadStart) := by
  intro state
  cases present : state.storage[storageId]? with
  | none => simp [landReceivingStorage,present,ConstructionResult.finalState]
  | some storage =>
      simp only [landReceivingStorage,present]
      split <;> rfl

private theorem keepsOutput_completed_landing (replacementId supersededId : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) :
    KeepsOutput (landCompletedReplacement replacementId supersededId count replacement superseded parentUpdate) := by
  apply keepsOutput_bind (lookupStorage replacement.storage)
  · exact keepsOutput_lookup_storage _
  · intro _
    apply keepsOutput_if
    · exact fun _ => rfl
    · apply keepsOutput_bind ConstructionM.get
      · exact keepsOutput_get
      · intro state
        apply keepsOutput_bind (protectedAbandonment _)
        · exact protectedAbandonment_stdout _
        · intro _
          apply keepsOutput_bind (landReceivingStorage _ _ _)
          · exact keepsOutput_land_receiving _ _ _
          · intro _
            apply keepsOutput_bind (replaceDestination replacementId _)
            · exact keepsOutput_replace_destination _ _
            · intro _
              cases parentUpdate with
              | none =>
                  apply keepsOutput_if
                  · exact keepsOutput_emit _
                  · exact keepsOutput_pure ()
              | some parent =>
                  apply keepsOutput_bind (replaceDestination parent.1 parent.2)
                  · exact keepsOutput_replace_destination _ _
                  · intro _
                    apply keepsOutput_if
                    · exact keepsOutput_emit _
                    · exact keepsOutput_pure ()

theorem landExitReplacement_stdout (replacementId : DestinationId) (state : ConstructionState) :
    (landExitReplacement replacementId state).finalState.stdout = state.stdout := by
  apply keepsOutput_bind (lookupDestination replacementId)
  · exact keepsOutput_lookup_destination replacementId
  · intro replacement
    cases replacement.use with
    | receiver => exact fun _ => rfl
    | child parentId => exact fun _ => rfl
    | replacement supersededId =>
      cases replacement.progress
      all_goals try exact fun _ => rfl
      rename_i count
      apply keepsOutput_bind (lookupDestination supersededId)
      · exact keepsOutput_lookup_destination supersededId
      · intro superseded
        cases superseded.progress
        all_goals try exact fun _ => rfl
        all_goals
          apply keepsOutput_if
          · exact fun _ => rfl
          · cases superseded.use with
            | receiver => exact keepsOutput_completed_landing _ _ _ _ _ _
            | replacement _ => exact fun _ => rfl
            | child parentId =>
                apply keepsOutput_bind (lookupDestination parentId)
                · exact keepsOutput_lookup_destination _
                · intro parent
                  cases parent.progress
                  all_goals try exact fun _ => rfl
                  apply keepsOutput_if
                  · exact fun _ => rfl
                  · exact keepsOutput_completed_landing _ _ _ _ _ _


abbrev PreservesEventPrefix (action : ConstructionM α) : Prop :=
  ∀ state, state.events <+: (action state).finalState.events

private theorem eventPrefix_bind (action : ConstructionM α) (remaining : α → ConstructionM β)
    (first : PreservesEventPrefix action) (next : ∀ value, PreservesEventPrefix (remaining value)) :
    PreservesEventPrefix (action >>= remaining) := by
  intro state
  have before := first state
  cases result : action state with
  | ok value after =>
      simp only [bind,result]
      have extended : state.events <+: after.events := by
        simpa [result,ConstructionResult.finalState] using before
      exact extended.trans (next value after)
  | fault reason after => simpa [bind,result,ConstructionResult.finalState] using before

private theorem eventPrefix_fault_bind (reason : ConstructionFault) (next : α → ConstructionM β) :
    PreservesEventPrefix (ConstructionM.fail reason >>= next) := fun _ => List.prefix_rfl

private theorem eventPrefix_get_bind (next : ConstructionState → ConstructionM α)
    (safe : ∀ state, state.events <+: (next state state).finalState.events) :
    PreservesEventPrefix (ConstructionM.get >>= next) := safe

private theorem eventPrefix_set_then (state updated : ConstructionState) (next : Unit → ConstructionM α)
    (before : state.events <+: updated.events)
    (safe : ∀ value, PreservesEventPrefix (next value)) :
    state.events <+: ((ConstructionM.set updated >>= next) state).finalState.events :=
  before.trans (safe () updated)

private theorem get_lookupStorage_swap (id : StorageId)
    (next : ConstructionState → ReceivingStorage → ConstructionM α) :
    (do let state ← ConstructionM.get; let storage ← lookupStorage id; next state storage) =
      (do let storage ← lookupStorage id; let state ← ConstructionM.get; next state storage) := by
  funext state
  simp only [ConstructionM.get,lookupStorage,bind]
  cases state.storage[id]? <;> rfl

private theorem eventPrefix_guard_then (state : ConstructionState) (condition : Prop)
    [Decidable condition] (reason : ConstructionFault) (next : Unit → ConstructionM α)
    (safe : state.events <+: (next () state).finalState.events) :
    state.events <+: ((do
      if condition then ConstructionM.fail reason
      next ()) state).finalState.events := by
  by_cases selected : condition
  · simp [selected,ConstructionM.fail,bind,ConstructionResult.finalState]
  · simpa only [selected,↓reduceIte] using safe

private theorem get_guard_swap (condition : Prop) [Decidable condition]
    (reason : ConstructionFault) (next : ConstructionState → ConstructionM α) :
    (do
      let state ← ConstructionM.get
      if condition then ConstructionM.fail reason
      next state) =
    (do
      if condition then ConstructionM.fail reason
      let state ← ConstructionM.get
      next state) := by
  funext state
  by_cases selected : condition <;>
    simp [selected,ConstructionM.get,ConstructionM.fail,bind]

private theorem eventPrefix_pure (value : α) : PreservesEventPrefix (pure value) := fun _ => List.prefix_rfl
private theorem eventPrefix_fail (reason : ConstructionFault) :
    PreservesEventPrefix (ConstructionM.fail (α := α) reason) := fun _ => List.prefix_rfl
private theorem eventPrefix_get : PreservesEventPrefix ConstructionM.get := fun _ => List.prefix_rfl

private theorem eventPrefix_lookupDestination (id : DestinationId) : PreservesEventPrefix (lookupDestination id) := by
  intro state
  simp only [lookupDestination,ConstructionM.get,bind]
  cases state.destinations[id]? <;> exact List.prefix_rfl

private theorem eventPrefix_lookupStorage (id : StorageId) : PreservesEventPrefix (lookupStorage id) := by
  intro state
  simp only [lookupStorage,ConstructionM.get,bind]
  cases state.storage[id]? <;> exact List.prefix_rfl

private theorem eventPrefix_replaceDestination (id : DestinationId) (destination : PendingDestination) :
    PreservesEventPrefix (replaceDestination id destination) := by
  intro state
  simp only [replaceDestination,ConstructionM.get,bind]
  split <;> exact List.prefix_rfl

private theorem eventPrefix_replaceStorage (id : StorageId) (storage : ReceivingStorage) :
    PreservesEventPrefix (replaceStorage id storage) := by
  intro state
  simp only [replaceStorage,ConstructionM.get,bind]
  split <;> exact List.prefix_rfl

private theorem eventPrefix_emit (event : ConstructionEvent) : PreservesEventPrefix (emit event) := by
  intro state
  exact List.prefix_append state.events [event]

private theorem eventPrefix_writableDestination (id : DestinationId) : PreservesEventPrefix (writableDestination id) := by
  apply eventPrefix_bind (lookupDestination id)
  · exact eventPrefix_lookupDestination id
  · intro destination
    apply eventPrefix_bind ConstructionM.get
    · exact eventPrefix_get
    · intro state current
      dsimp only
      split <;> exact List.prefix_rfl

private theorem eventPrefix_if (condition : Prop) [Decidable condition]
    (yes no : ConstructionM α) (first : PreservesEventPrefix yes) (second : PreservesEventPrefix no) :
    PreservesEventPrefix (if condition then yes else no) := by
  by_cases selected : condition
  · simpa only [selected,↓reduceIte] using first
  · simpa only [selected,↓reduceIte] using second

theorem reserveStorage_events_prefix (bytes : ByteArray) (count : Nat) :
    PreservesEventPrefix (reserveStorage bytes count) := fun _ => List.prefix_rfl

theorem appendStdout_events_prefix (bytes : ByteArray) :
    PreservesEventPrefix (appendStdout bytes) := fun _ => List.prefix_rfl

theorem adaptDestinationType_events_prefix (id : DestinationId) (ty : Ty) :
    PreservesEventPrefix (adaptDestinationType id ty) := by
  apply eventPrefix_bind (writableDestination id)
  · exact eventPrefix_writableDestination id
  · intro destination
    cases destination.progress
    all_goals try exact fun _ => List.prefix_rfl
    all_goals
      apply eventPrefix_if
      · exact fun _ => List.prefix_rfl
      · exact eventPrefix_replaceDestination _ _


private theorem eventPrefix_protectedAbandonment (discarded : List PendingDestination) :
    PreservesEventPrefix (protectedAbandonment discarded) := by
  intro state
  obtain ⟨suffix,equal⟩ := protectedAbandonment_events discarded state
  exact ⟨suffix,equal.symm⟩

theorem restoreReceivingLayout_events_prefix (id : DestinationId) (layout : ReceivingLayout)  :
    PreservesEventPrefix (restoreReceivingLayout id layout) := by
  apply eventPrefix_bind (writableDestination id)
  · exact eventPrefix_writableDestination id
  · intro destination
    cases destination.progress
    all_goals try exact fun _ => List.prefix_rfl
    apply eventPrefix_if
    · exact fun _ => List.prefix_rfl
    · exact eventPrefix_replaceDestination _ _

theorem removeConstructionHeader_events_prefix (id : DestinationId)  :
    PreservesEventPrefix (removeConstructionHeader id) := by
  apply eventPrefix_bind (writableDestination id)
  · exact eventPrefix_writableDestination id
  · intro destination
    cases destination.progress
    all_goals try exact eventPrefix_fail .protocol
    apply eventPrefix_if
    · exact eventPrefix_fail .protocol
    · apply eventPrefix_bind (lookupStorage destination.storage)
      · exact eventPrefix_lookupStorage _
      · intro storage
        apply eventPrefix_if
        · exact eventPrefix_fail .storage
        · apply eventPrefix_bind (replaceStorage destination.storage _)
          · exact eventPrefix_replaceStorage _ _
          · intro _
            apply eventPrefix_bind (replaceDestination id _)
            · exact eventPrefix_replaceDestination _ _
            · intro _; exact eventPrefix_emit _



private theorem eventPrefix_landReceiving (storageId : StorageId) (receivingStart payloadStart : Nat) :
    PreservesEventPrefix (landReceivingStorage storageId receivingStart payloadStart) := by
  intro state
  cases present : state.storage[storageId]? with
  | none => simp [landReceivingStorage,present,ConstructionResult.finalState]
  | some storage =>
      simp only [landReceivingStorage,present]
      split <;> exact List.prefix_rfl

private theorem eventPrefix_completedLanding (replacementId supersededId : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) :
    PreservesEventPrefix (landCompletedReplacement replacementId supersededId count replacement superseded parentUpdate) := by
  apply eventPrefix_bind (lookupStorage replacement.storage)
  · exact eventPrefix_lookupStorage _
  · intro _
    apply eventPrefix_if
    · exact fun _ => List.prefix_rfl
    · apply eventPrefix_bind ConstructionM.get
      · exact eventPrefix_get
      · intro state
        apply eventPrefix_bind (protectedAbandonment _)
        · exact eventPrefix_protectedAbandonment _
        · intro _
          apply eventPrefix_bind (landReceivingStorage _ _ _)
          · exact eventPrefix_landReceiving _ _ _
          · intro _
            apply eventPrefix_bind (replaceDestination replacementId _)
            · exact eventPrefix_replaceDestination _ _
            · intro _
              cases parentUpdate with
              | none =>
                  apply eventPrefix_if
                  · exact eventPrefix_emit _
                  · exact eventPrefix_pure ()
              | some parent =>
                  apply eventPrefix_bind (replaceDestination parent.1 parent.2)
                  · exact eventPrefix_replaceDestination _ _
                  · intro _
                    apply eventPrefix_if
                    · exact eventPrefix_emit _
                    · exact eventPrefix_pure ()

theorem landExitReplacement_events_prefix (replacementId : DestinationId)  :
    PreservesEventPrefix (landExitReplacement replacementId) := by
  apply eventPrefix_bind (lookupDestination replacementId)
  · exact eventPrefix_lookupDestination replacementId
  · intro replacement
    cases replacement.use with
    | receiver => exact fun _ => List.prefix_rfl
    | child parentId => exact fun _ => List.prefix_rfl
    | replacement supersededId =>
      cases replacement.progress
      all_goals try exact fun _ => List.prefix_rfl
      rename_i count
      apply eventPrefix_bind (lookupDestination supersededId)
      · exact eventPrefix_lookupDestination supersededId
      · intro superseded
        cases superseded.progress
        all_goals try exact fun _ => List.prefix_rfl
        all_goals
          apply eventPrefix_if
          · exact fun _ => List.prefix_rfl
          · cases superseded.use with
            | receiver => exact eventPrefix_completedLanding _ _ _ _ _ _
            | replacement _ => exact fun _ => List.prefix_rfl
            | child parentId =>
                apply eventPrefix_bind (lookupDestination parentId)
                · exact eventPrefix_lookupDestination _
                · intro parent
                  cases parent.progress
                  all_goals try exact fun _ => List.prefix_rfl
                  apply eventPrefix_if
                  · exact fun _ => List.prefix_rfl
                  · exact eventPrefix_completedLanding _ _ _ _ _ _



theorem abandonPreservingExit_events_prefix (id replacementId : DestinationId) :
    PreservesEventPrefix (abandonPreservingExit id replacementId) := by
  intro state
  obtain ⟨suffix,equal⟩ := abandonPreservingExit_events state id replacementId
  exact ⟨suffix,equal.symm⟩

theorem recordCopy_events_prefix (source : CopySource) (id : DestinationId) :
    PreservesEventPrefix (recordCopy source id) := by
  unfold recordCopy
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value


theorem writeElement_events_prefix (id : DestinationId) (bytes : ByteArray) :
    PreservesEventPrefix (writeElement id bytes) := by
  unfold writeElement
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem finishDestination_events_prefix (id : DestinationId) :
    PreservesEventPrefix (finishDestination id) := by
  unfold finishDestination
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem attachChild_events_prefix (parent child : DestinationId) :
    PreservesEventPrefix (attachChild parent child) := by
  unfold attachChild
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem attachExtension_events_prefix (parent child : DestinationId) :
    PreservesEventPrefix (attachExtension parent child) := by
  unfold attachExtension
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem attachElementExtension_events_prefix (parent child : DestinationId) :
    PreservesEventPrefix (attachElementExtension parent child) := by
  unfold attachElementExtension
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem publishElementDestination_events_prefix (id : DestinationId) :
    PreservesEventPrefix (publishElementDestination id) := by
  unfold publishElementDestination
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem retireRepeatedSource_events_prefix (parent source : DestinationId) :
    PreservesEventPrefix (retireRepeatedSource parent source) := by
  unfold retireRepeatedSource
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem truncateConstructionStorage_events_prefix (storage : StorageId) (start finish count : Nat) (owner : Option DestinationId) (retainSlots : Bool) :
    PreservesEventPrefix (truncateConstructionStorage storage start finish count owner retainSlots) := by
  unfold truncateConstructionStorage
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem prepareNamedBinding_events_prefix (id : DestinationId) (ty : Ty) :
    PreservesEventPrefix (prepareNamedBinding id ty) := by
  unfold prepareNamedBinding
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem fitStagedDestination_events_prefix (id : DestinationId) :
    PreservesEventPrefix (fitStagedDestination id) := by
  unfold fitStagedDestination
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value


theorem openChild_events_prefix (parent : DestinationId) (ty : Ty) (layout : ReceivingLayout) :
    PreservesEventPrefix (openChild parent ty layout) := by
  unfold openChild
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact reserveStorage_events_prefix _ _
    | with_reducible exact reserveStorage_events_prefix _ _ _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_set_then
    | with_reducible exact List.prefix_rfl
    | with_reducible apply eventPrefix_get_bind
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem openExtension_events_prefix (parent : DestinationId) (request : ConstructionRequest) (count : Option Nat) :
    PreservesEventPrefix (openExtension parent request count) := by
  unfold openExtension
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact reserveStorage_events_prefix _ _
    | with_reducible exact reserveStorage_events_prefix _ _ _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_set_then
    | with_reducible exact List.prefix_rfl
    | with_reducible apply eventPrefix_get_bind
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem openElementExtension_events_prefix (parent : DestinationId) (ty : Ty) (layout : ReceivingLayout) (count : Option Nat) (receiver : Loc) :
    PreservesEventPrefix (openElementExtension parent ty layout count receiver) := by
  unfold openElementExtension
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact reserveStorage_events_prefix _ _
    | with_reducible exact reserveStorage_events_prefix _ _ _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_set_then
    | with_reducible exact List.prefix_rfl
    | with_reducible apply eventPrefix_get_bind
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem openExitReplacement_events_prefix (id : DestinationId) :
    PreservesEventPrefix (openExitReplacement id) := by
  unfold openExitReplacement
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact reserveStorage_events_prefix _ _
    | with_reducible exact reserveStorage_events_prefix _ _ _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_set_then
    | with_reducible exact List.prefix_rfl
    | with_reducible apply eventPrefix_get_bind
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

private theorem eventPrefix_forInLoop (values : List α)
    (body : (value : α) → value ∈ values → β → ConstructionM (ForInStep β))
    (safe : ∀ value member accumulator, PreservesEventPrefix (body value member accumulator))
    (remaining : List α) (accumulator : β) (inside : ∃ earlier, earlier ++ remaining = values) :
    PreservesEventPrefix (List.forIn'.loop values body remaining accumulator inside) := by
  induction remaining generalizing accumulator with
  | nil => exact eventPrefix_pure _
  | cons value rest ih =>
      simp only [List.forIn'.loop]
      apply eventPrefix_bind
      · exact safe _ _ _
      · intro step
        cases step with
        | done accumulator => exact eventPrefix_pure _
        | yield accumulator => exact ih _ _

private theorem eventPrefix_forIn (values : List α) (accumulator : β)
    (body : α → β → ConstructionM (ForInStep β))
    (safe : ∀ value accumulator, PreservesEventPrefix (body value accumulator)) :
    PreservesEventPrefix (forIn values accumulator body) := by
  apply eventPrefix_forInLoop
  intro value member accumulator
  exact safe value accumulator

private theorem eventPrefix_foreach (values : List α) (body : α → ConstructionM Unit)
    (safe : ∀ value, PreservesEventPrefix (body value)) :
    PreservesEventPrefix (do for value in values do body value) := by
  apply eventPrefix_bind
  · apply eventPrefix_forInLoop
    intro value member accumulator
    apply eventPrefix_bind
    · exact safe value
    · intro _; exact eventPrefix_pure _
  · intro _; exact eventPrefix_pure _


private theorem eventPrefix_openDestinationWith (policy : StagingPolicy) (storage : StorageId)
    (capability : Core.Destination Ty) (layout : ReceivingLayout) (count : Option Nat) :
    PreservesEventPrefix (openDestinationWith policy storage capability layout count) := by
  cases policy <;> cases layout <;> cases count
  all_goals unfold openDestinationWith
  all_goals simp only [get_lookupStorage_swap,get_guard_swap]
  all_goals repeat' first
    | with_reducible exact eventPrefix_pure _ _
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact reserveStorage_events_prefix _ _
    | with_reducible exact reserveStorage_events_prefix _ _ _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | apply eventPrefix_guard_then
    | with_reducible apply eventPrefix_set_then
    | exact List.prefix_rfl
    | with_reducible apply eventPrefix_get_bind
    | intro value
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split

theorem openDestination_events_prefix (storage : StorageId) (capability : Core.Destination Ty)
    (layout : ReceivingLayout) (count : Option Nat) :
    PreservesEventPrefix (openDestination storage capability layout count) :=
  eventPrefix_openDestinationWith _ _ _ _ _

theorem openDestinationDirect_events_prefix (storage : StorageId) (capability : Core.Destination Ty)
    (layout : ReceivingLayout) (count : Option Nat) :
    PreservesEventPrefix (openDestinationDirect storage capability layout count) :=
  eventPrefix_openDestinationWith _ _ _ _ _


private theorem eventPrefix_publishReady (id : DestinationId) :
    PreservesEventPrefix (publishReady id) := by
  unfold publishReady
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact reserveStorage_events_prefix _ _
    | with_reducible exact reserveStorage_events_prefix _ _ _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_set_then
    | with_reducible exact List.prefix_rfl
    | with_reducible apply eventPrefix_get_bind
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem publishOperation_events_prefix (ids : List DestinationId) :
    PreservesEventPrefix (publishOperation ids) := by
  apply eventPrefix_get_bind
  intro state
  cases preflightPublication state ids with
  | error reason => exact List.prefix_rfl
  | ok value =>
      cases value
      exact eventPrefix_foreach ids publishReady eventPrefix_publishReady state


theorem abandonDestination_events_prefix (id : DestinationId) :
    PreservesEventPrefix (abandonDestination id) := by
  unfold abandonDestination
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact reserveStorage_events_prefix _ _
    | with_reducible exact reserveStorage_events_prefix _ _ _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_set_then
    | with_reducible exact List.prefix_rfl
    | with_reducible apply eventPrefix_get_bind
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem stageDestination_events_prefix (id : DestinationId) :
    PreservesEventPrefix (stageDestination id) := by
  unfold stageDestination
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact reserveStorage_events_prefix _ _
    | with_reducible exact reserveStorage_events_prefix _ _ _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_set_then
    | with_reducible exact List.prefix_rfl
    | with_reducible apply eventPrefix_get_bind
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem abandonTree_events_prefix (id : DestinationId) :
    PreservesEventPrefix (abandonTree id) := by
  unfold abandonTree
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact reserveStorage_events_prefix _ _
    | with_reducible exact reserveStorage_events_prefix _ _ _
    | with_reducible exact abandonDestination_events_prefix _
    | with_reducible apply eventPrefix_forIn
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_set_then
    | with_reducible exact List.prefix_rfl
    | with_reducible apply eventPrefix_get_bind
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem adaptConstructionDestination_events_prefix (id : DestinationId) (ty : Ty) (request : ConstructionRequest) :
    PreservesEventPrefix (adaptConstructionDestination id ty request) := by
  unfold adaptConstructionDestination
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact removeConstructionHeader_events_prefix _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem finishConstructionAdaptation_events_prefix (id : DestinationId) :
    PreservesEventPrefix (finishConstructionAdaptation id) := by
  unfold finishConstructionAdaptation
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact removeConstructionHeader_events_prefix _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

theorem normalizeProducerDestination_events_prefix (id : DestinationId) (ty : Ty) :
    PreservesEventPrefix (normalizeProducerDestination id ty) := by
  unfold normalizeProducerDestination
  repeat' first
    | with_reducible exact eventPrefix_pure _
    | with_reducible exact eventPrefix_fault_bind _ _
    | with_reducible exact eventPrefix_fail _
    | with_reducible exact removeConstructionHeader_events_prefix _
    | with_reducible exact eventPrefix_get
    | with_reducible exact eventPrefix_writableDestination _
    | with_reducible exact eventPrefix_lookupDestination _
    | with_reducible exact eventPrefix_lookupStorage _
    | with_reducible exact eventPrefix_replaceDestination _ _
    | with_reducible exact eventPrefix_replaceStorage _ _
    | with_reducible exact eventPrefix_emit _
    | dsimp only
    | with_reducible apply eventPrefix_bind
    | with_reducible apply eventPrefix_if
    | split
    | intro value

private theorem keepsOutput_removeHeader (id : DestinationId) : KeepsOutput (removeConstructionHeader id) :=
  removeConstructionHeader_stdout id

private theorem keepsOutput_fault_bind (reason : ConstructionFault) (next : α → ConstructionM β) :
    KeepsOutput (ConstructionM.fail reason >>= next) := fun _ => rfl

theorem adaptConstructionDestination_stdout (id : DestinationId) (ty : Ty) (request : ConstructionRequest) :
    ∀ state, (adaptConstructionDestination id ty request state).finalState.stdout = state.stdout := by
  change KeepsOutput (adaptConstructionDestination id ty request)
  unfold adaptConstructionDestination
  repeat' first
    | with_reducible exact keepsOutput_pure _
    | with_reducible exact keepsOutput_fault_bind _ _
    | with_reducible exact keepsOutput_fail _
    | with_reducible exact keepsOutput_get
    | with_reducible exact keepsOutput_writable_destination _
    | with_reducible exact keepsOutput_lookup_destination _
    | with_reducible exact keepsOutput_lookup_storage _
    | with_reducible exact keepsOutput_replace_destination _ _
    | with_reducible exact keepsOutput_replace_storage _ _
    | with_reducible exact keepsOutput_emit _
    | with_reducible exact keepsOutput_removeHeader _
    | dsimp only
    | with_reducible apply keepsOutput_bind
    | with_reducible apply keepsOutput_if
    | split
    | intro value


theorem finishConstructionAdaptation_stdout (id : DestinationId) :
    ∀ state, (finishConstructionAdaptation id state).finalState.stdout = state.stdout := by
  change KeepsOutput (finishConstructionAdaptation id)
  unfold finishConstructionAdaptation
  repeat' first
    | with_reducible exact keepsOutput_pure _
    | with_reducible exact keepsOutput_fault_bind _ _
    | with_reducible exact keepsOutput_fail _
    | with_reducible exact keepsOutput_get
    | with_reducible exact keepsOutput_writable_destination _
    | with_reducible exact keepsOutput_lookup_destination _
    | with_reducible exact keepsOutput_lookup_storage _
    | with_reducible exact keepsOutput_replace_destination _ _
    | with_reducible exact keepsOutput_replace_storage _ _
    | with_reducible exact keepsOutput_emit _
    | with_reducible exact keepsOutput_removeHeader _
    | dsimp only
    | with_reducible apply keepsOutput_bind
    | with_reducible apply keepsOutput_if
    | split
    | intro value


theorem normalizeProducerDestination_stdout (id : DestinationId) (ty : Ty) :
    ∀ state, (normalizeProducerDestination id ty state).finalState.stdout = state.stdout := by
  change KeepsOutput (normalizeProducerDestination id ty)
  unfold normalizeProducerDestination
  repeat' first
    | with_reducible exact keepsOutput_pure _
    | with_reducible exact keepsOutput_fault_bind _ _
    | with_reducible exact keepsOutput_fail _
    | with_reducible exact keepsOutput_get
    | with_reducible exact keepsOutput_writable_destination _
    | with_reducible exact keepsOutput_lookup_destination _
    | with_reducible exact keepsOutput_lookup_storage _
    | with_reducible exact keepsOutput_replace_destination _ _
    | with_reducible exact keepsOutput_replace_storage _ _
    | with_reducible exact keepsOutput_emit _
    | with_reducible exact keepsOutput_removeHeader _
    | dsimp only
    | with_reducible apply keepsOutput_bind
    | with_reducible apply keepsOutput_if
    | split
    | intro value


def destinationBeginIds (events : List ConstructionEvent) : List DestinationId :=
  events.filterMap fun event => match event with
    | .begin id => some id
    | _ => none

def DestinationBegins (state : ConstructionState) : Prop :=
  destinationBeginIds state.events = List.range state.destinations.size

abbrev PreservesDestinationBegins (action : ConstructionM α) : Prop :=
  ∀ state, DestinationBegins state → DestinationBegins (action state).finalState

abbrev DestinationBeginFrame (before after : ConstructionState) : Prop :=
  destinationBeginIds after.events = destinationBeginIds before.events ∧
    after.destinations.size = before.destinations.size

abbrev FramesDestinationBegins (action : ConstructionM α) : Prop :=
  ∀ state, DestinationBeginFrame state (action state).finalState

theorem initial_destination_begins : DestinationBegins ConstructionState.initial := rfl

theorem FramesDestinationBegins.preserves (action : ConstructionM α)
    (frame : FramesDestinationBegins action) : PreservesDestinationBegins action := by
  intro state valid
  rcases frame state with ⟨events, size⟩
  simpa only [DestinationBegins, events, size] using valid

private theorem beginFrame_refl (state : ConstructionState) : DestinationBeginFrame state state := ⟨rfl,rfl⟩

private theorem beginFrame_trans {before middle after : ConstructionState}
    (first : DestinationBeginFrame before middle) (second : DestinationBeginFrame middle after) :
    DestinationBeginFrame before after := ⟨second.1.trans first.1,second.2.trans first.2⟩

private theorem beginFrame_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : FramesDestinationBegins action) (remaining : ∀ value, FramesDestinationBegins (next value)) :
    FramesDestinationBegins (action >>= next) := by
  intro state
  cases result : action state with
  | ok value after =>
      simp only [bind,result]
      apply beginFrame_trans _ (remaining value after)
      simpa only [result,ConstructionResult.finalState] using first state
  | fault kind after => simpa only [bind,result,ConstructionResult.finalState] using first state

private theorem beginFrame_pure (value : α) : FramesDestinationBegins (pure value) := beginFrame_refl
private theorem beginFrame_fail (kind : ConstructionFault) :
    FramesDestinationBegins (ConstructionM.fail (α := α) kind) := beginFrame_refl
private theorem beginFrame_fault_bind (kind : ConstructionFault) (next : α → ConstructionM β) :
    FramesDestinationBegins (ConstructionM.fail kind >>= next) := beginFrame_refl
private theorem beginFrame_get : FramesDestinationBegins ConstructionM.get := beginFrame_refl

private theorem beginFrame_lookupDestination (id : DestinationId) :
    FramesDestinationBegins (lookupDestination id) := by
  intro state
  simp only [lookupDestination,ConstructionM.get,bind]
  cases state.destinations[id]? <;> exact beginFrame_refl state

private theorem beginFrame_lookupStorage (id : StorageId) : FramesDestinationBegins (lookupStorage id) := by
  intro state
  simp only [lookupStorage,ConstructionM.get,bind]
  cases state.storage[id]? <;> exact beginFrame_refl state

private theorem beginFrame_replaceDestination (id : DestinationId) (destination : PendingDestination) :
    FramesDestinationBegins (replaceDestination id destination) := by
  intro state
  simp only [replaceDestination,ConstructionM.get,bind]
  split
  · exact ⟨rfl, by simp [ConstructionM.set,ConstructionResult.finalState]⟩
  · exact beginFrame_refl state

private theorem beginFrame_replaceStorage (id : StorageId) (storage : ReceivingStorage) :
    FramesDestinationBegins (replaceStorage id storage) := by
  intro state
  simp only [replaceStorage,ConstructionM.get,bind]
  split <;> exact ⟨rfl,rfl⟩

private theorem beginFrame_emit (event : ConstructionEvent)
    (notBegin : (match event with | .begin _ => false | _ => true) = true) :
    FramesDestinationBegins (emit event) := by
  intro state
  cases event <;> simp_all [emit,ConstructionM.get,ConstructionM.set,bind,
    ConstructionResult.finalState,DestinationBeginFrame,destinationBeginIds]

private theorem beginFrame_writableDestination (id : DestinationId) :
    FramesDestinationBegins (writableDestination id) := by
  apply beginFrame_bind (lookupDestination id)
  · exact beginFrame_lookupDestination id
  · intro destination
    apply beginFrame_bind ConstructionM.get
    · exact beginFrame_get
    · intro state current
      dsimp only
      split <;> exact beginFrame_refl current

private theorem beginFrame_if (condition : Prop) [Decidable condition] (yes no : ConstructionM α)
    (first : FramesDestinationBegins yes) (second : FramesDestinationBegins no) :
    FramesDestinationBegins (if condition then yes else no) := by
  by_cases selected : condition
  · simpa only [selected,↓reduceIte] using first
  · simpa only [selected,↓reduceIte] using second

theorem reserveStorage_destination_begins_frame (bytes : ByteArray) (count : Nat) :
    FramesDestinationBegins (reserveStorage bytes count) := fun _ => ⟨rfl,rfl⟩

theorem appendStdout_destination_begins_frame (bytes : ByteArray) :
    FramesDestinationBegins (appendStdout bytes) := fun _ => ⟨rfl,rfl⟩

theorem recordCopy_destination_begins_frame (source : CopySource) (id : DestinationId) :
    FramesDestinationBegins (recordCopy source id) := by
  unfold recordCopy
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem writeElement_destination_begins_frame (id : DestinationId) (bytes : ByteArray) :
    FramesDestinationBegins (writeElement id bytes) := by
  unfold writeElement
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem finishDestination_destination_begins_frame (id : DestinationId) :
    FramesDestinationBegins (finishDestination id) := by
  unfold finishDestination
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem attachChild_destination_begins_frame (parent child : DestinationId) :
    FramesDestinationBegins (attachChild parent child) := by
  unfold attachChild
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem attachExtension_destination_begins_frame (parent child : DestinationId) :
    FramesDestinationBegins (attachExtension parent child) := by
  unfold attachExtension
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem attachElementExtension_destination_begins_frame (parent child : DestinationId) :
    FramesDestinationBegins (attachElementExtension parent child) := by
  unfold attachElementExtension
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem publishElementDestination_destination_begins_frame (id : DestinationId) :
    FramesDestinationBegins (publishElementDestination id) := by
  unfold publishElementDestination
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem retireRepeatedSource_destination_begins_frame (parent source : DestinationId) :
    FramesDestinationBegins (retireRepeatedSource parent source) := by
  unfold retireRepeatedSource
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem truncateConstructionStorage_destination_begins_frame (storage : StorageId) (start finish count : Nat) (owner : Option DestinationId) (retainSlots : Bool) :
    FramesDestinationBegins (truncateConstructionStorage storage start finish count owner retainSlots) := by
  unfold truncateConstructionStorage
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem prepareNamedBinding_destination_begins_frame (id : DestinationId) (ty : Ty) :
    FramesDestinationBegins (prepareNamedBinding id ty) := by
  unfold prepareNamedBinding
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem fitStagedDestination_destination_begins_frame (id : DestinationId) :
    FramesDestinationBegins (fitStagedDestination id) := by
  unfold fitStagedDestination
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem removeConstructionHeader_destination_begins_frame (id : DestinationId) :
    FramesDestinationBegins (removeConstructionHeader id) := by
  unfold removeConstructionHeader
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem restoreReceivingLayout_destination_begins_frame (id : DestinationId) (layout : ReceivingLayout) :
    FramesDestinationBegins (restoreReceivingLayout id layout) := by
  apply beginFrame_bind (writableDestination id)
  · exact beginFrame_writableDestination id
  · intro destination
    cases destination.progress
    all_goals try exact beginFrame_refl
    apply beginFrame_if
    · exact beginFrame_refl
    · exact beginFrame_replaceDestination _ _

theorem adaptDestinationType_destination_begins_frame (id : DestinationId) (ty : Ty) :
    FramesDestinationBegins (adaptDestinationType id ty) := by
  unfold adaptDestinationType
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem adaptConstructionDestination_destination_begins_frame (id : DestinationId) (ty : Ty) (request : ConstructionRequest) :
    FramesDestinationBegins (adaptConstructionDestination id ty request) := by
  unfold adaptConstructionDestination
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem finishConstructionAdaptation_destination_begins_frame (id : DestinationId) :
    FramesDestinationBegins (finishConstructionAdaptation id) := by
  unfold finishConstructionAdaptation
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | with_reducible exact removeConstructionHeader_destination_begins_frame _
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem normalizeProducerDestination_destination_begins_frame (id : DestinationId) (ty : Ty) :
    FramesDestinationBegins (normalizeProducerDestination id ty) := by
  unfold normalizeProducerDestination
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | with_reducible exact removeConstructionHeader_destination_begins_frame _
    | dsimp only
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

private theorem beginFrame_get_bind (next : ConstructionState → ConstructionM α)
    (safe : ∀ state, DestinationBeginFrame state (next state state).finalState) :
    FramesDestinationBegins (ConstructionM.get >>= next) := safe

private theorem beginFrame_set_then (state updated : ConstructionState) (next : Unit → ConstructionM α)
    (before : DestinationBeginFrame state updated)
    (safe : ∀ value, FramesDestinationBegins (next value)) :
    DestinationBeginFrame state ((ConstructionM.set updated >>= next) state).finalState :=
  beginFrame_trans before (safe () updated)

private theorem beginFrame_protectedAbandonment (discarded : List PendingDestination) :
    FramesDestinationBegins (protectedAbandonment discarded) := by
  intro state
  induction discarded generalizing state with
  | nil => exact beginFrame_refl state
  | cons destination rest ih =>
      simp only [protectedAbandonment]
      split
      · apply beginFrame_trans _ (ih _)
        simp [DestinationBeginFrame,destinationBeginIds]
      · exact beginFrame_refl state

theorem abandonPreservingExit_destination_begins_frame (id replacement : DestinationId) :
    FramesDestinationBegins (abandonPreservingExit id replacement) := by
  intro state
  unfold abandonPreservingExit
  simp only [ConstructionM.get,bind]
  cases protectedExitDiscarded state id replacement with
  | error _ => exact beginFrame_refl state
  | ok discarded => exact beginFrame_protectedAbandonment discarded state

theorem landReceivingStorage_destination_begins_frame (storage : StorageId) (receivingStart payloadStart : Nat) :
    FramesDestinationBegins (landReceivingStorage storage receivingStart payloadStart) := by
  intro state
  cases present : state.storage[storage]? with
  | none => simp [landReceivingStorage,present,ConstructionResult.finalState,DestinationBeginFrame]
  | some receiving =>
      simp only [landReceivingStorage,present]
      split <;> exact ⟨rfl,rfl⟩

private theorem beginFrame_forInLoop (values : List α)
    (body : (value : α) → value ∈ values → β → ConstructionM (ForInStep β))
    (safe : ∀ value member accumulator, FramesDestinationBegins (body value member accumulator))
    (remaining : List α) (accumulator : β) (inside : ∃ earlier, earlier ++ remaining = values) :
    FramesDestinationBegins (List.forIn'.loop values body remaining accumulator inside) := by
  induction remaining generalizing accumulator with
  | nil => exact beginFrame_pure _
  | cons value rest ih =>
      simp only [List.forIn'.loop]
      apply beginFrame_bind
      · exact safe _ _ _
      · intro step
        cases step with
        | done accumulator => exact beginFrame_pure _
        | yield accumulator => exact ih _ _

private theorem beginFrame_forIn (values : List α) (accumulator : β)
    (body : α → β → ConstructionM (ForInStep β))
    (safe : ∀ value accumulator, FramesDestinationBegins (body value accumulator)) :
    FramesDestinationBegins (forIn values accumulator body) := by
  apply beginFrame_forInLoop
  intro value member accumulator
  exact safe value accumulator

private theorem beginFrame_foreach (values : List α) (body : α → ConstructionM Unit)
    (safe : ∀ value, FramesDestinationBegins (body value)) :
    FramesDestinationBegins (do for value in values do body value) := by
  apply beginFrame_bind
  · apply beginFrame_forInLoop
    intro value member accumulator
    apply beginFrame_bind
    · exact safe value
    · intro _; exact beginFrame_pure _
  · intro _; exact beginFrame_pure _


theorem abandonDestination_destination_begins_frame (id : DestinationId) :
    FramesDestinationBegins (abandonDestination id) := by
  unfold abandonDestination
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact reserveStorage_destination_begins_frame _ _
    | with_reducible exact reserveStorage_destination_begins_frame _ _ _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_set_then
    | with_reducible exact ⟨rfl,rfl⟩
    | with_reducible apply beginFrame_get_bind
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem stageDestination_destination_begins_frame (id : DestinationId) :
    FramesDestinationBegins (stageDestination id) := by
  unfold stageDestination
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact reserveStorage_destination_begins_frame _ _
    | with_reducible exact reserveStorage_destination_begins_frame _ _ _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_set_then
    | with_reducible exact ⟨rfl,rfl⟩
    | with_reducible apply beginFrame_get_bind
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem abandonTree_destination_begins_frame (id : DestinationId) :
    FramesDestinationBegins (abandonTree id) := by
  unfold abandonTree
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact reserveStorage_destination_begins_frame _ _
    | with_reducible exact reserveStorage_destination_begins_frame _ _ _
    | with_reducible exact abandonDestination_destination_begins_frame _
    | with_reducible apply beginFrame_forIn
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_set_then
    | with_reducible exact ⟨rfl,rfl⟩
    | with_reducible apply beginFrame_get_bind
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

private theorem beginFrame_completedLanding (replacementId supersededId : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) :
    FramesDestinationBegins (landCompletedReplacement replacementId supersededId count replacement superseded parentUpdate) := by
  apply beginFrame_bind (lookupStorage replacement.storage)
  · exact beginFrame_lookupStorage _
  · intro _
    apply beginFrame_if
    · exact beginFrame_refl
    · apply beginFrame_bind ConstructionM.get
      · exact beginFrame_get
      · intro state
        apply beginFrame_bind (protectedAbandonment _)
        · exact beginFrame_protectedAbandonment _
        · intro _
          apply beginFrame_bind (landReceivingStorage _ _ _)
          · exact landReceivingStorage_destination_begins_frame _ _ _
          · intro _
            apply beginFrame_bind (replaceDestination replacementId _)
            · exact beginFrame_replaceDestination _ _
            · intro _
              cases parentUpdate with
              | none =>
                  apply beginFrame_if
                  · exact beginFrame_emit _ rfl
                  · exact beginFrame_pure ()
              | some parent =>
                  apply beginFrame_bind (replaceDestination parent.1 parent.2)
                  · exact beginFrame_replaceDestination _ _
                  · intro _
                    apply beginFrame_if
                    · exact beginFrame_emit _ rfl
                    · exact beginFrame_pure ()

theorem landExitReplacement_destination_begins_frame (replacementId : DestinationId)  :
    FramesDestinationBegins (landExitReplacement replacementId) := by
  apply beginFrame_bind (lookupDestination replacementId)
  · exact beginFrame_lookupDestination replacementId
  · intro replacement
    cases replacement.use with
    | receiver => exact beginFrame_refl
    | child parentId => exact beginFrame_refl
    | replacement supersededId =>
      cases replacement.progress
      all_goals try exact beginFrame_refl
      rename_i count
      apply beginFrame_bind (lookupDestination supersededId)
      · exact beginFrame_lookupDestination supersededId
      · intro superseded
        cases superseded.progress
        all_goals try exact beginFrame_refl
        all_goals
          apply beginFrame_if
          · exact beginFrame_refl
          · cases superseded.use with
            | receiver => exact beginFrame_completedLanding _ _ _ _ _ _
            | replacement _ => exact beginFrame_refl
            | child parentId =>
                apply beginFrame_bind (lookupDestination parentId)
                · exact beginFrame_lookupDestination _
                · intro parent
                  cases parent.progress
                  all_goals try exact beginFrame_refl
                  apply beginFrame_if
                  · exact beginFrame_refl
                  · exact beginFrame_completedLanding _ _ _ _ _ _



private theorem beginFrame_publishReady (id : DestinationId) :
    FramesDestinationBegins (publishReady id) := by
  unfold publishReady
  repeat' first
    | with_reducible exact beginFrame_pure _
    | with_reducible exact beginFrame_fault_bind _ _
    | with_reducible exact beginFrame_fail _
    | with_reducible exact reserveStorage_destination_begins_frame _ _
    | with_reducible exact reserveStorage_destination_begins_frame _ _ _
    | with_reducible exact beginFrame_get
    | with_reducible exact beginFrame_writableDestination _
    | with_reducible exact beginFrame_lookupDestination _
    | with_reducible exact beginFrame_lookupStorage _
    | with_reducible exact beginFrame_replaceDestination _ _
    | with_reducible exact beginFrame_replaceStorage _ _
    | with_reducible exact beginFrame_emit _ rfl
    | dsimp only
    | with_reducible apply beginFrame_set_then
    | with_reducible exact ⟨rfl,rfl⟩
    | with_reducible apply beginFrame_get_bind
    | with_reducible apply beginFrame_bind
    | with_reducible apply beginFrame_if
    | split
    | intro value

theorem publishOperation_destination_begins_frame (ids : List DestinationId) :
    FramesDestinationBegins (publishOperation ids) := by
  apply beginFrame_get_bind
  intro state
  cases preflightPublication state ids with
  | error reason => exact ⟨rfl,rfl⟩
  | ok value =>
      cases value
      exact beginFrame_foreach ids publishReady beginFrame_publishReady state


end Goose.Construct
