import Goose.Core.Construction

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
  | published (count : Nat)
  | attached (count : Nat)
  | abandoned
  deriving DecidableEq, Repr

inductive DestinationUse
  | receiver
  | child (parent : DestinationId)
  deriving DecidableEq, Repr

structure PendingDestination where
  capability : Destination
  storage : StorageId
  layout : ReceivingLayout
  use : DestinationUse
  progress : DestinationProgress
  deriving Repr

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

private def hasPrefix (layout : ReceivingLayout) (request : Request) : Bool :=
  layout == .packed && request == .value

private def available (layout : ReceivingLayout) (storage : ReceivingStorage) (count : Nat) : Bool :=
  match layout with
  | .limited capacity => storage.publishedCount + count ≤ capacity
  | .fixed expected => count ≤ expected
  | .packed => count < 2 ^ 32
  | .elements => true

private def active (destination : PendingDestination) : Bool :=
  match destination.progress with
  | .open _ | .suspended _ _ | .built _ => true
  | .published _ | .attached _ | .abandoned => false

def openDestination (storageId : StorageId) (capability : Destination)
    (layout : ReceivingLayout) (knownCount : Option Nat) : ConstructionM DestinationId := do
  if capability.request == .register then ConstructionM.fail .protocol
  let storage ← lookupStorage storageId
  let state ← ConstructionM.get
  if state.destinations.any (fun d => d.storage == storageId && active d) then
    ConstructionM.fail .ownership
  if let some count := knownCount then
    if !available layout storage count then ConstructionM.fail .capacity
  else
    match layout with
    | .limited _ => ConstructionM.fail .protocol
    | _ => pure ()
  let id := state.destinations.size
  let capability := { capability with id := id, start := storage.bytes.size }
  let destination : PendingDestination := ⟨capability, storageId, layout, .receiver, .open 0⟩
  ConstructionM.set { state with destinations := state.destinations.push destination }
  if hasPrefix layout capability.request then
    replaceStorage storageId { storage with bytes := storage.bytes ++ lengthPrefix }
  emit (.begin id)
  pure id

def writeElement (id : DestinationId) (bytes : ByteArray) : ConstructionM Unit := do
  let destination ← lookupDestination id
  match destination.progress with
  | .open count =>
      let storage ← lookupStorage destination.storage
      if !available destination.layout storage (count + 1) then ConstructionM.fail .capacity
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
      if !available parent.layout storage (count + 1) then ConstructionM.fail .capacity
      let state ← ConstructionM.get
      let id := state.destinations.size
      let capability := { parent.capability with
        id := id, logicalType := logicalType, request := .value, start := storage.bytes.size }
      let child : PendingDestination := ⟨capability, parent.storage, layout, .child parentId, .open 0⟩
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

private def publishReady (id : DestinationId) : ConstructionM Unit := do
  let destination ← lookupDestination id
  match destination.progress, destination.use with
  | .built count, .receiver =>
      let storage ← lookupStorage destination.storage
      let publishedCount := match destination.layout with
        | .elements | .limited _ => storage.publishedCount + count
        | .packed | .fixed _ => count
      replaceStorage destination.storage { storage with publishedCount := publishedCount }
      replaceDestination id { destination with progress := .published count }
      emit (.publish id)
  | _, _ => ConstructionM.fail .protocol

def publishOperation (ids : List DestinationId) : ConstructionM Unit := do
  if ids.eraseDups != ids then ConstructionM.fail .ownership
  for id in ids do
    let destination ← lookupDestination id
    match destination.progress, destination.use with
    | .built _, .receiver => pure ()
    | _, _ => ConstructionM.fail .protocol
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
  | .suspended _ _ => ConstructionM.fail .protocol
  | .published _ | .attached _ | .abandoned => ConstructionM.fail .protocol

def abandonTree (id : DestinationId) : ConstructionM Unit := do
  let parent ← lookupDestination id
  let state ← ConstructionM.get
  let descendants := state.destinations.toList.reverse.filter fun destination =>
    destination.storage == parent.storage &&
      id ≤ destination.capability.id && active destination
  for destination in descendants do
    let current ← lookupDestination destination.capability.id
    match current.progress with
    | .suspended count _ =>
        replaceDestination current.capability.id { current with progress := .open count }
    | _ => pure ()
    abandonDestination destination.capability.id

end Goose.Construct
