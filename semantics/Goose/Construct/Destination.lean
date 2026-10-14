import Goose.Construct.Syntax

namespace Goose.Construct
open Goose.Core

inductive ReceivingLayout
  | packed
  | elements
  | fixed (count : Nat)
  | limited (capacity : Nat)
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

private def lengthPrefix : ByteArray := ⟨#[0, 0, 0, 0]⟩

private def hasPrefix (layout : ReceivingLayout) (request : ConstructionRequest) : Bool :=
  layout == .packed && request == .value

private def available (layout : ReceivingLayout) (storage : ReceivingStorage) (count : Nat) : Bool :=
  match layout with
  | .limited capacity => storage.publishedCount + count ≤ capacity
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
  | .published _ | .attached _ | .abandoned => false

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
    | .limited _, none => do pure (.staged storageId (← reserveStorage))
    | _, _ => pure (DestinationBacking.direct storageId)
  let state ← ConstructionM.get
  let storage ← lookupStorage backing.writeStorage
  let id := state.destinations.size
  let capability := { capability with id := id, start := storage.bytes.size }
  let destination : PendingDestination := ⟨capability, backing, layout, .receiver, .open 0⟩
  ConstructionM.set { state with destinations := state.destinations.push destination }
  if hasPrefix layout capability.request then
    replaceStorage backing.writeStorage { storage with bytes := storage.bytes ++ lengthPrefix }
  emit (.begin id)
  match backing with
  | .staged _ _ => emit (.stage id)
  | .direct _ => pure ()
  pure id

def writeElement (id : DestinationId) (bytes : ByteArray) : ConstructionM Unit := do
  let destination ← lookupDestination id
  match destination.progress with
  | .open count =>
      let storage ← lookupStorage destination.storage
      if !writingAvailable destination storage (count + 1) then ConstructionM.fail .capacity
      replaceStorage destination.storage { storage with bytes := storage.bytes ++ bytes }
      replaceDestination id { destination with progress := .open (count + 1) }
      emit (.write id count)
  | _ => ConstructionM.fail .protocol

def openChild (parentId : DestinationId) (logicalType : Ty) (layout : ReceivingLayout) :
    ConstructionM DestinationId := do
  let parent ← lookupDestination parentId
  match parent.progress with
  | .open count =>
      let storage ← lookupStorage parent.storage
      if !writingAvailable parent storage (count + 1) then ConstructionM.fail .capacity
      let state ← ConstructionM.get
      let id := state.destinations.size
      let capability := { parent.capability with
        id := id, logicalType := logicalType, request := .value, start := storage.bytes.size }
      let child : PendingDestination := ⟨capability, .direct parent.storage, layout, .child parentId, .open 0⟩
      ConstructionM.set { state with destinations := state.destinations.push child }
      replaceDestination parentId { parent with progress := .suspended count id }
      if hasPrefix layout .value then
        replaceStorage parent.storage { storage with bytes := storage.bytes ++ lengthPrefix }
      emit (.begin id)
      pure id
  | _ => ConstructionM.fail .protocol

private def patchCount (bytes : ByteArray) (start count : Nat) : ByteArray := Id.run do
  let mut result := bytes
  for offset in [0:4] do
    result := result.set! (start + offset) (UInt8.ofNat (count / 2 ^ (offset * 8) % 256))
  return result

def finishDestination (id : DestinationId) : ConstructionM Unit := do
  let destination ← lookupDestination id
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
  let parent ← lookupDestination parentId
  let child ← lookupDestination childId
  match parent.progress, child.progress, child.use with
  | .suspended count expected, .built childCount, .child owner =>
      if expected != childId || owner != parentId || child.storage != parent.storage then
        ConstructionM.fail .ownership
      replaceDestination childId { child with progress := .attached childCount }
      replaceDestination parentId { parent with progress := .open (count + 1) }
      emit (.write parentId count)
  | _, _, _ => ConstructionM.fail .protocol

private def checkPublication (id : DestinationId) : ConstructionM Unit := do
  let destination ← lookupDestination id
  match destination.progress, destination.use with
  | .built count, .receiver =>
      let receiver ← lookupStorage destination.backing.receiverStorage
      requireFit destination receiver count
  | _, _ => ConstructionM.fail .protocol
where
  requireFit (destination : PendingDestination) (receiver : ReceivingStorage) (count : Nat) : ConstructionM Unit := do
    if !available destination.layout receiver count then ConstructionM.fail .capacity
    let _ ← lookupStorage destination.storage

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
            pure { receiver with bytes := receiver.bytes ++ stage.bytes }
      let publishedCount := match destination.layout with
        | .elements | .limited _ => storage.publishedCount + count
        | .packed | .fixed _ => count
      replaceStorage destination.backing.receiverStorage { storage with publishedCount := publishedCount }
      replaceDestination id { destination with progress := .published count }
      match destination.backing with
      | .direct _ => pure ()
      | .staged _ stageId => replaceStorage stageId ⟨ByteArray.empty, 0⟩
      emit (.publish id)
  | _, _ => ConstructionM.fail .protocol

def publishOperation (ids : List DestinationId) : ConstructionM Unit := do
  if ids.eraseDups != ids then ConstructionM.fail .ownership
  for id in ids do checkPublication id
  for id in ids do publishReady id

def abandonDestination (id : DestinationId) : ConstructionM Unit := do
  let destination ← lookupDestination id
  match destination.progress with
  | .open _ | .built _ =>
      let storage ← lookupStorage destination.storage
      replaceStorage destination.storage
        { storage with bytes := storage.bytes.extract 0 destination.capability.start }
      replaceDestination id { destination with progress := .abandoned }
      emit (.abandon id)
  | .suspended _ _ | .exiting _ _ => ConstructionM.fail .protocol
  | .published _ | .attached _ | .abandoned => ConstructionM.fail .protocol

private def descendantOf (destinations : Array PendingDestination) (ancestor : DestinationId)
    (id : DestinationId) : Bool := Id.run do
  let mut current := id
  for _ in [0:destinations.size] do
    if current == ancestor then return true
    let some destination := destinations[current]? | return false
    match destination.use with
    | .receiver | .replacement _ => return false
    | .child parent => current := parent
  return false

def abandonTree (id : DestinationId) : ConstructionM Unit := do
  let parent ← lookupDestination id
  match parent.progress with
  | .open _ | .built _ | .suspended _ _ => pure ()
  | .exiting _ _ | .published _ | .attached _ | .abandoned => ConstructionM.fail .protocol
  let state ← ConstructionM.get
  let descendants := state.destinations.toList.reverse.filter fun destination =>
    descendantOf state.destinations id destination.capability.id && active destination
  for destination in descendants do
    match destination.progress with
    | .exiting _ _ => ConstructionM.fail .protocol
    | _ => pure ()
  for destination in descendants do
    let current ← lookupDestination destination.capability.id
    match current.progress with
    | .suspended count _ =>
        replaceDestination current.capability.id { current with progress := .open count }
    | _ => pure ()
    abandonDestination destination.capability.id

def openExitReplacement (supersededId : DestinationId) : ConstructionM DestinationId := do
  let superseded ← lookupDestination supersededId
  let count ← match superseded.progress with
    | .open count | .built count | .suspended count _ => pure count
    | .exiting _ _ | .published _ | .attached _ | .abandoned => ConstructionM.fail .protocol
  let storage ← lookupStorage superseded.storage
  let state ← ConstructionM.get
  let id := state.destinations.size
  let capability := { superseded.capability with id := id, start := storage.bytes.size }
  let replacement : PendingDestination :=
    ⟨capability, superseded.backing, superseded.layout, .replacement supersededId, .open 0⟩
  ConstructionM.set { state with destinations := state.destinations.push replacement }
  replaceDestination supersededId { superseded with progress := .exiting count id }
  if hasPrefix superseded.layout superseded.capability.request then
    replaceStorage superseded.storage { storage with bytes := storage.bytes ++ lengthPrefix }
  emit (.begin id)
  pure id

def landingBytes (bytes : ByteArray) (receivingStart payloadStart : Nat) : ByteArray :=
  bytes.extract 0 receivingStart ++ bytes.extract payloadStart bytes.size

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
  let storage ← lookupStorage replacement.storage
  if replacement.capability.start < superseded.capability.start then ConstructionM.fail .ownership
  let state ← ConstructionM.get
  let discarded := state.destinations.toList.reverse.filter fun destination =>
    descendantOf state.destinations supersededId destination.capability.id && active destination
  for destination in discarded do
    replaceDestination destination.capability.id { destination with progress := .abandoned }
    emit (.abandon destination.capability.id)
  let landed := landingBytes storage.bytes superseded.capability.start replacement.capability.start
  replaceStorage replacement.storage { storage with bytes := landed }
  replaceDestination replacementId { replacement with
    capability := { replacement.capability with start := superseded.capability.start }
    use := superseded.use
    progress := .built count }
  if let some (parentId, parent) := parentUpdate then
    replaceDestination parentId parent
  if superseded.capability.start < replacement.capability.start then
    emit (.relocate replacementId .exitValue)

end Goose.Construct
