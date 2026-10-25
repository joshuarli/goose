import Goose.Construct.Runtime
import Init.Data.ByteArray.Lemmas

namespace Goose.Proofs.Construct
open Goose.Construct

theorem landing_preserves_prefix (bytes : ByteArray) (receivingStart payloadStart : Nat)
    (inside : receivingStart ≤ bytes.size) :
    (landingBytes bytes receivingStart payloadStart).extract 0 receivingStart =
      bytes.extract 0 receivingStart := by
  unfold landingBytes
  apply ByteArray.extract_append_eq_left
  simp [ByteArray.size_extract, Nat.min_eq_left inside]

theorem landing_preserves_payload (bytes : ByteArray) (receivingStart payloadStart : Nat)
    (inside : receivingStart ≤ bytes.size) :
    (landingBytes bytes receivingStart payloadStart).extract receivingStart
      (landingBytes bytes receivingStart payloadStart).size =
      bytes.extract payloadStart bytes.size := by
  unfold landingBytes
  apply ByteArray.extract_append_eq_right
  · simp [ByteArray.size_extract, Nat.min_eq_left inside]
  · exact ByteArray.size_append

theorem landing_top (bytes : ByteArray) (receivingStart payloadStart : Nat)
    (inside : receivingStart ≤ bytes.size) :
    (landingBytes bytes receivingStart payloadStart).size =
      receivingStart + (bytes.size - payloadStart) := by
  simp [landingBytes, ByteArray.size_append, ByteArray.size_extract, Nat.min_eq_left inside]

theorem terminal_keeps_prefix (kind : ConstructionFault) (state : ConstructionState) :
    ConstructionM.fail (α := Unit) kind state = .fault kind state := rfl

theorem terminal_skips_remaining (kind : ConstructionFault) (state : ConstructionState)
    (remaining : Unit → ConstructionM Unit) :
    ((ConstructionM.fail kind >>= remaining) state) = .fault kind state := rfl


theorem publication_rejection_keeps_prefix (state : ConstructionState) (ids : List Goose.Core.DestinationId)
    (kind : ConstructionFault) (rejected : preflightPublication state ids = .error kind) :
    publishOperation ids state = .fault kind state := by
  simp [publishOperation, ConstructionM.get, rejected, bind, ConstructionM.fail]


theorem landed_storage_prefix (storage : ReceivingStorage) (receivingStart payloadStart : Nat)
    (inside : receivingStart ≤ storage.bytes.size) :
    (storage.landExit receivingStart payloadStart).bytes.extract 0 receivingStart =
      storage.bytes.extract 0 receivingStart :=
  landing_preserves_prefix storage.bytes receivingStart payloadStart inside

theorem landed_storage_payload (storage : ReceivingStorage) (receivingStart payloadStart : Nat)
    (inside : receivingStart ≤ storage.bytes.size) :
    (storage.landExit receivingStart payloadStart).bytes.extract receivingStart
      (storage.landExit receivingStart payloadStart).bytes.size =
      storage.bytes.extract payloadStart storage.bytes.size :=
  landing_preserves_payload storage.bytes receivingStart payloadStart inside

theorem landed_storage_publication (storage : ReceivingStorage) (receivingStart payloadStart : Nat) :
    (storage.landExit receivingStart payloadStart).publishedCount = storage.publishedCount := rfl


theorem receiving_landing_success (state : ConstructionState) (storageId : Goose.Core.StorageId)
    (storage : ReceivingStorage) (receivingStart payloadStart : Nat)
    (present : state.storage[storageId]? = some storage)
    (ordered : receivingStart ≤ payloadStart) (inside : payloadStart ≤ storage.bytes.size) :
    landReceivingStorage storageId receivingStart payloadStart state =
      .ok () { state with
        storage := state.storage.set! storageId (storage.landExit receivingStart payloadStart) } := by
  simp [landReceivingStorage, present, ordered, inside]

theorem receiving_landing_payload (state : ConstructionState) (storageId : Goose.Core.StorageId)
    (storage : ReceivingStorage) (receivingStart payloadStart : Nat)
    (present : state.storage[storageId]? = some storage)
    (ordered : receivingStart ≤ payloadStart) (inside : payloadStart ≤ storage.bytes.size) :
    ((landReceivingStorage storageId receivingStart payloadStart state).finalState.storage[storageId]?).map
      (fun landed => landed.bytes.extract receivingStart landed.bytes.size) =
      some (storage.bytes.extract payloadStart storage.bytes.size) := by
  rw [receiving_landing_success state storageId storage receivingStart payloadStart present ordered inside]
  obtain ⟨inBounds, _⟩ := Array.getElem?_eq_some_iff.mp present
  simp only [ConstructionResult.finalState, Array.set!, Array.getElem?_setIfInBounds_self_of_lt inBounds, Option.map_some]
  rw [landed_storage_payload storage receivingStart payloadStart (Nat.le_trans ordered inside)]

theorem receiving_landing_outside (state : ConstructionState) (storageId other : Goose.Core.StorageId)
    (storage : ReceivingStorage) (receivingStart payloadStart : Nat)
    (present : state.storage[storageId]? = some storage)
    (ordered : receivingStart ≤ payloadStart) (inside : payloadStart ≤ storage.bytes.size)
    (different : storageId ≠ other) :
    (landReceivingStorage storageId receivingStart payloadStart state).finalState.storage[other]? =
      state.storage[other]? := by
  rw [receiving_landing_success state storageId storage receivingStart payloadStart present ordered inside]
  exact Array.getElem?_setIfInBounds_ne different


theorem cleanup_consumed_destination (state : ExecutionState) (id : Goose.Core.DestinationId)
    (destination : PendingDestination) (origin : Goose.Core.OriginId) (carriers : List Goose.Construct.Carrier)
    (present : state.construction.destinations[id]? = some destination)
    (consumed : activeProgress destination.progress = false) :
    cleanupDestination origin id carriers state = .ok () state := by
  simp [cleanupDestination, getDestination, EvalM.get, bind, pure, present, consumed]

theorem runtime_stop_skips_remaining (reason : Goose.Core.Stop) (state : ExecutionState)
    (remaining : Unit → EvalM Unit) :
    ((EvalM.stop reason >>= remaining) state) = .stop reason state := rfl

theorem runtime_escape_skips_remaining (target : Goose.Construct.ExitAddress) (carriers : List Goose.Construct.Carrier)
    (state : ExecutionState) (remaining : Unit → EvalM Unit) :
    (((fun state => ExecutionStep.escape target carriers state) >>= remaining) state) =
      .escape target carriers state := rfl

end Goose.Proofs.Construct
