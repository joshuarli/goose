import Goose.Construct.Destination
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

end Goose.Proofs.Construct
