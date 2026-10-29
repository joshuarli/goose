import Goose.Proofs.ConstructionExitNewestLeaf
import Goose.Proofs.ConstructionExitDirectByteLoop
import Goose.Proofs.ConstructionExitCompletionReservation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage

theorem direct_byte_write_then_cancel (state : ConstructionState)
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
      (∀ index, index < selected → final.destinations[index]? = written.destinations[index]?) ∧
      (∀ other, other ≠ token → final.exitReservations[other]? = state.exitReservations[other]?) := by
  obtain ⟨written, nextStorage, write, nextPresent, nextStored, nextCurrent⟩ :=
    packed_receiver_write_step state selected count row storage byte present stored opened packed adaptation use current fits
  let nextRow := { row with progress := DestinationProgress.open (count + 1), writeEnd := row.writeEnd + 1 }
  have frame := writeElement_reservation_frame selected ⟨#[byte]⟩ state lifecycle.1
  rw [write] at frame
  simp only [ConstructionResult.finalState] at frame
  have destinationLife := writeElement_destination_lifecycle_invariant selected ⟨#[byte]⟩ state lifecycle.1
  rw [write] at destinationLife
  simp only [ConstructionResult.finalState] at destinationLife
  have writtenLife : ReservationLifecycleInvariant written :=
    ⟨destinationLife, destinationReservationStateValid_frame state written frame lifecycle.2⟩
  have preservedTicket : written.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
    rw [frame.tickets]
    exact ticket
  have indexing := writeElement_preserves_indexing selected ⟨#[byte]⟩ state
  rw [write] at indexing
  simp only [ConstructionResult.finalState] at indexing
  have writtenNewest : written.destinations.size = selected + 1 := indexing.1.trans newest
  have rowPresent : written.destinations[selected]? = some nextRow := nextPresent
  have rowStored : written.storage[nextRow.storage]? = some nextStorage := nextStored
  obtain ⟨final, cancel, rows, tickets⟩ := cancel_newest_direct_receiver_preserves_older written token incoming selected selected
    (count + 1) snapshot nextRow nextStorage preservedTicket nextCurrent rowPresent use (Or.inl rfl) rowStored writtenNewest direct writtenLife
  refine ⟨written, final, write, cancel, rows, ?_⟩
  intro other different
  exact (tickets other different).trans (congrArg (fun entries => entries[other]?) frame.tickets)

#print axioms direct_byte_write_then_cancel

end Goose.Proofs.ConstructionAcceptedExecution
