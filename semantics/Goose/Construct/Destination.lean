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

structure PendingDestination where
  capability : Core.Destination Ty
  backing : DestinationBacking
  layout : ReceivingLayout
  use : DestinationUse
  progress : DestinationProgress
  writeEnd : Nat
  rollbackEnd : Nat
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
  | .direct _ => available destination.layout storage count
  | .staged _ _ => true

private def active (destination : PendingDestination) : Bool :=
  match destination.progress with
  | .open _ | .suspended _ _ | .built _ | .exiting _ _ => true
  | .published _ | .attached _ | .abandoned | .cancelled => false

def openDestination (storageId : StorageId) (capability : Core.Destination Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) : ConstructionM DestinationId := do
  let storage ← lookupStorage storageId
  let state ← ConstructionM.get
  if state.destinations.any (fun d => (d.storage == storageId || d.backing.receiverStorage == storageId) && active d) then
    ConstructionM.fail .ownership
  if let some count := knownCount then
    if !available layout storage count then ConstructionM.fail .capacity
  else
    pure ()
  let backing ← match layout, knownCount with
    | .limited _ _, none => do pure (.staged storageId (← reserveStorage))
    | _, _ => pure (DestinationBacking.direct storageId)
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
    match layout with | .limited _ _ => storage.bytes.size | _ => start⟩
  ConstructionM.set { state with destinations := state.destinations.push destination }
  if hasPrefix layout capability.request then
    replaceStorage backing.writeStorage { storage with bytes := storage.bytes ++ lengthPrefix }
  emit (.begin id)
  match backing with
  | .staged _ _ => emit (.stage id)
  | .direct _ => pure ()
  pure id

def writeElement (id : DestinationId) (bytes : ByteArray) : ConstructionM Unit := do
  let destination ← writableDestination id
  match destination.progress with
  | .open count =>
      let storage ← lookupStorage destination.storage
      if !writingAvailable destination storage (count + 1) then ConstructionM.fail .capacity
      match destination.layout, destination.backing with
      | .limited _ slotBytes, .direct _ =>
          if bytes.size != slotBytes then ConstructionM.fail .protocol
      | _, _ => pure ()
      match destination.use with
      | .child parentId =>
          let parent ← lookupDestination parentId
          match parent.layout, parent.progress, parent.backing, destination.backing with
          | .limited capacity slotBytes, .suspended parentCount _, .direct _, .direct _ =>
              if parentCount + count + 1 > capacity then ConstructionM.fail .capacity
              if bytes.size != slotBytes then ConstructionM.fail .protocol
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
        match parent.layout with | .limited _ _ => storage.bytes.size | _ => capability.start⟩
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
      let some receiver := state.storage[destination.backing.receiverStorage]? | throw .storage
      if !available destination.layout receiver count then throw .capacity
      if (state.storage[destination.storage]?).isNone then throw .storage
  | _, _ => throw .protocol

def preflightPublication (state : ConstructionState) (ids : List DestinationId) :
    Except ConstructionFault Unit := do
  if ids.eraseDups != ids then throw .ownership
  for id in ids do publicationCheck state id

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
  | .published _ | .attached _ | .abandoned | .cancelled => ConstructionM.fail .protocol

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
  | .exiting _ _ | .published _ | .attached _ | .abandoned | .cancelled => ConstructionM.fail .protocol
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
    | .exiting _ _ | .published _ | .attached _ | .abandoned | .cancelled => ConstructionM.fail .protocol
  let storage ← lookupStorage superseded.storage
  let state ← ConstructionM.get
  let id := state.destinations.size
  let capability := { superseded.capability with id := id, start := storage.bytes.size }
  let replacement : PendingDestination :=
    ⟨capability, superseded.backing, superseded.layout, .replacement supersededId, .open 0,
      capability.start + (if hasPrefix superseded.layout superseded.capability.request then 4 else 0),
      capability.start⟩
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
  let _ ← lookupStorage replacement.storage
  if replacement.capability.start < superseded.capability.start then ConstructionM.fail .ownership
  let state ← ConstructionM.get
  let discarded := state.destinations.toList.reverse.filter fun destination =>
    destination.capability.id != replacementId &&
      descendantOf state.destinations supersededId destination.capability.id && active destination
  for destination in discarded do
    replaceDestination destination.capability.id { destination with progress := .abandoned }
    emit (.abandon destination.capability.id)
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
      match backing, parent.layout with
      | .direct _, .limited _ _ => storage.bytes.size
      | _, _ => start⟩
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

end Goose.Construct
