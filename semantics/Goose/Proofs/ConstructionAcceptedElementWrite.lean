import Goose.Proofs.ConstructionAcceptedOpenDestination
import Goose.Proofs.ConstructionElementWriteTransition
import Goose.Proofs.ConstructionLayoutFuel
import Goose.Proofs.ExitExecutionLandingPayload

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Proofs.ExitExecution

private def elementWriteBytes (before payload : ByteArray) (point : Nat) : ByteArray :=
  before.extract 0 point ++ payload ++ before.extract (point + payload.size) before.size

private theorem elementWriteBytes_size (before payload : ByteArray) (point : Nat)
    (bounded : point ≤ before.size) :
    (elementWriteBytes before payload point).size = max before.size (point + payload.size) := by
  simp only [elementWriteBytes, ByteArray.size_append, ByteArray.size_extract, Nat.sub_zero,
    Nat.min_eq_left bounded, Nat.min_self]
  omega

private theorem elementWriteBytes_prefix (before payload : ByteArray) (point : Nat)
    (bounded : point ≤ before.size) :
    RelocatedBytes before (elementWriteBytes before payload point) 0 0 point := by
  have prefixSize : (before.extract 0 point).size = point := by simp [ByteArray.size_extract, bounded]
  refine ⟨by omega, ?_, ?_⟩
  · rw [elementWriteBytes_size before payload point bounded]
    omega
  · simp only [Nat.zero_add, elementWriteBytes]
    rw [ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_left prefixSize.symm

private theorem elementWriteBytes_payload (before payload : ByteArray) (point : Nat)
    (bounded : point ≤ before.size) :
    RelocatedBytes payload (elementWriteBytes before payload point) 0 point payload.size := by
  have prefixSize : (before.extract 0 point).size = point := by simp [ByteArray.size_extract, bounded]
  refine ⟨by omega, ?_, ?_⟩
  · rw [elementWriteBytes_size before payload point bounded]
    omega
  · simp only [Nat.zero_add, elementWriteBytes]
    rw [ByteArray.extract_append]
    have left : ((before.extract 0 point ++ payload).extract point (point + payload.size)) = payload :=
      ByteArray.extract_append_eq_right prefixSize.symm (by rw [prefixSize])
    rw [left]
    simp [ByteArray.size_append, prefixSize]

theorem writeElement_open_backing (layout : LayoutEnv) (before : ExecutionState)
    (after : ConstructionState) (id : Nat) (ty : Ty) (count : Nat) (payload : ByteArray)
    (ready : OpenDestinationBacking layout before id ty count)
    (encoded : ∃ fuel, packedEnd fuel layout ready.element payload 0 = .ok payload.size)
    (executed : writeElement id payload before.construction = .ok () after) :
    Nonempty (OpenDestinationBacking layout { before with construction := after } id ty (count + 1)) := by
  have transition := Goose.Proofs.ConstructionStorage.writeElement_transition id payload before.construction
  rw [executed] at transition
  cases transition with
  | written destination storage actualCount present stored opened =>
    have sameRow := Option.some.inj (present.symm.trans ready.present)
    subst destination
    have sameStorage := Option.some.inj (stored.symm.trans ready.bytes)
    subst storage
    have sameCount := DestinationProgress.open.inj (opened.symm.trans ready.opened)
    subst actualCount
    let updated := elementWriteBytes ready.storage.bytes payload ready.destination.writeEnd
    have preserved := elementWriteBytes_prefix ready.storage.bytes payload ready.destination.writeEnd ready.bounded
    have appended := elementWriteBytes_payload ready.storage.bytes payload ready.destination.writeEnd ready.bounded
    have previous : elementsEnd ready.fuel layout ready.element count updated
        (destinationPayloadStart ready.destination) = .ok ready.destination.writeEnd := by
      simpa only [Nat.zero_add] using preserved.elementsEnd ready.fuel layout ready.element count
        (destinationPayloadStart ready.destination) ready.destination.writeEnd (by simpa only [Nat.zero_add] using ready.scan) (Nat.le_refl _)
    obtain ⟨elementFuel, element⟩ := encoded
    have last : packedEnd elementFuel layout ready.element updated ready.destination.writeEnd =
        .ok (ready.destination.writeEnd + payload.size) := by
      simpa only [Nat.zero_add, Nat.add_zero] using
        appended.packedEnd elementFuel layout ready.element 0 payload.size (by simpa only [Nat.zero_add] using element) (Nat.le_refl _)
    obtain ⟨fuel, scanned⟩ := Goose.Proofs.ConstructionRepresentation.elementsEnd_append_one
      ready.fuel elementFuel layout ready.element count updated (destinationPayloadStart ready.destination)
      ready.destination.writeEnd (ready.destination.writeEnd + payload.size) previous last
    refine ⟨⟨{ ready.destination with progress := .open (count + 1), writeEnd := ready.destination.writeEnd + payload.size },
      { ready.storage with bytes := updated }, ?_, ?_, ready.logicalType, rfl,
      ready.element, ready.elementType, fuel, scanned, ?_, ?_⟩⟩
    · exact Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp ready.present).1
    · exact Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp ready.bytes).1
    · change ready.destination.writeEnd + payload.size ≤ updated.size
      rw [elementWriteBytes_size ready.storage.bytes payload ready.destination.writeEnd ready.bounded]
      exact Nat.le_max_right _ _
    · change ready.destination.rollbackEnd ≤ updated.size
      rw [elementWriteBytes_size ready.storage.bytes payload ready.destination.writeEnd ready.bounded]
      exact Nat.le_trans ready.rollback (Nat.le_max_left _ _)

#print axioms writeElement_open_backing

end Goose.Proofs.ConstructionAcceptedExecution
