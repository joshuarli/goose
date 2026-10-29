import Goose.Proofs.ConstructionExitWrittenCancel
import Goose.Proofs.ConstructionExitLeafStorage

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage

theorem direct_byte_write_cancel_frame (state : ConstructionState)
    (token incoming selected count : Nat) (snapshot row : PendingDestination) (storage : ReceivingStorage) (byte : UInt8)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (present : state.destinations[selected]? = some row) (stored : state.storage[row.storage]? = some storage)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (adaptation : row.adaptation = none) (use : row.use = .receiver)
    (current : destinationCurrent state selected = .ok selected) (fits : count + 1 < 2 ^ 32)
    (newest : state.destinations.size = selected + 1) (direct : selected = snapshot.capability.id)
    (lifecycle : ReservationLifecycleInvariant state) :
    ∃ written final,
      writeElement selected ⟨#[byte]⟩ state = .ok () written ∧
      (do cancelExitReservation token []; releaseExitReservation token) written = .ok () final ∧
      (∀ index, index < selected → final.destinations[index]? = state.destinations[index]?) ∧
      (∀ index, index ≠ row.storage → final.storage[index]? = state.storage[index]?) ∧
      (∀ other, other ≠ token → final.exitReservations[other]? = state.exitReservations[other]?) := by
  obtain ⟨written, final, write, cancel, rows, tickets⟩ := direct_byte_write_then_cancel state token incoming selected count snapshot row storage byte
    ticket present stored opened packed adaptation use current fits newest direct lifecycle
  obtain ⟨otherWritten, nextStorage, otherWrite, nextPresent, nextStored, nextCurrent⟩ :=
    packed_receiver_write_step state selected count row storage byte present stored opened packed adaptation use current fits
  have sameWritten : otherWritten = written := (ConstructionResult.ok.inj (otherWrite.symm.trans write)).2
  subst otherWritten
  let nextRow := { row with progress := DestinationProgress.open (count + 1), writeEnd := row.writeEnd + 1 }
  have metadata := writeElement_reservation_frame selected ⟨#[byte]⟩ state lifecycle.1
  rw [write] at metadata
  simp only [ConstructionResult.finalState] at metadata
  have destLife := writeElement_destination_lifecycle_invariant selected ⟨#[byte]⟩ state lifecycle.1
  rw [write] at destLife
  simp only [ConstructionResult.finalState] at destLife
  have writtenLife : ReservationLifecycleInvariant written :=
    ⟨destLife, destinationReservationStateValid_frame state written metadata lifecycle.2⟩
  have writtenTicket : written.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
    rw [metadata.tickets]
    exact ticket
  have indexing := writeElement_preserves_indexing selected ⟨#[byte]⟩ state
  rw [write] at indexing
  simp only [ConstructionResult.finalState] at indexing
  have writtenNewest : written.destinations.size = selected + 1 := indexing.1.trans newest
  have nextFound : written.destinations[selected]? = some nextRow := nextPresent
  have nextStore : written.storage[nextRow.storage]? = some nextStorage := nextStored
  have leaf := newest_active_destination_is_leaf written selected nextRow nextFound (by simp [activeRow, nextRow])
    writtenNewest writtenLife.1.2.1 writtenLife.1.2.2.2
  have writable := Goose.Proofs.ExitExecution.receiver_destination_writable written selected nextRow nextFound use
  obtain ⟨otherFinal, otherCancel, storageFrame⟩ := cancel_leaf_preserves_other_storage written token incoming selected selected (count + 1)
    snapshot nextRow nextStorage writtenTicket nextCurrent nextFound (writtenLife.1.2.1 selected nextRow nextFound)
    (Or.inl rfl) writable nextStore leaf direct writtenLife
  have sameFinal : otherFinal = final := (ConstructionResult.ok.inj (otherCancel.symm.trans cancel)).2
  subst otherFinal
  have writeRows : ∀ index, index < selected → written.destinations[index]? = state.destinations[index]? := by
    intro index earlier
    have transition := writeElement_transition selected ⟨#[byte]⟩ state
    rw [write] at transition
    cases transition with
    | written actual oldStorage actualCount actualFound actualStored actualOpened =>
      have different : selected ≠ index := Nat.ne_of_gt earlier
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, different]
  have writeStorage : ∀ index, index ≠ row.storage → written.storage[index]? = state.storage[index]? := by
    intro index different
    have transition := writeElement_transition selected ⟨#[byte]⟩ state
    rw [write] at transition
    cases transition with
    | written actual oldStorage actualCount actualFound actualStored actualOpened =>
      have sameRow : actual = row := Option.some.inj (actualFound.symm.trans present)
      subst actual
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm different]
  refine ⟨written, final, write, cancel, ?_, ?_, tickets⟩
  · intro index earlier
    exact (rows index earlier).trans (writeRows index earlier)
  · intro index different
    exact (storageFrame index different).trans (writeStorage index different)

#print axioms direct_byte_write_cancel_frame

end Goose.Proofs.ConstructionAcceptedExecution
