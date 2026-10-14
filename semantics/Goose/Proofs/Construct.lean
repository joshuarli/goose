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

end Goose.Proofs.Construct
