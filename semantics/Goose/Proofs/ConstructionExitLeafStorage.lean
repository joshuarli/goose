import Goose.Proofs.ConstructionExitAbandonLeaf

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem cancel_leaf_preserves_other_storage (state : ConstructionState)
    (token incoming reserved selected count : Nat) (snapshot row : PendingDestination) (storage : ReceivingStorage)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (present : state.destinations[selected]? = some row) (identity : row.capability.id = selected)
    (phase : row.progress = .open count ∨ row.progress = .built count)
    (writable : destinationCanWrite state selected = true)
    (stored : state.storage[row.storage]? = some storage)
    (leaf : treeRows state selected = [row]) (direct : reserved = snapshot.capability.id)
    (lifecycle : ReservationLifecycleInvariant state) :
    ∃ final, (do cancelExitReservation token []; releaseExitReservation token) state = .ok () final ∧
      ∀ index, index ≠ row.storage → final.storage[index]? = state.storage[index]? := by
  let cleaned := abandonRowState state selected row storage
  have tree : abandonTree selected state = .ok () cleaned :=
    abandon_leaf_success state selected count row storage present identity phase writable stored leaf
  have active : activeRow row = true := by rcases phase with phase | phase <;> simp [activeRow, phase]
  have frame := abandonTree_reservation_frame selected state lifecycle.1
  have tickets : cleaned.exitReservations = state.exitReservations := by
    simpa only [tree, ConstructionResult.finalState] using frame.tickets
  have inside : token < cleaned.exitReservations.size := by
    rw [tickets]
    exact (Array.getElem?_eq_some_iff.mp ticket).1
  let cancelled := { cleaned with
    destinationResumptions := (selected, snapshot) :: cleaned.destinationResumptions
    exitReservations := cleaned.exitReservations.set! token .restored }
  let final := { cancelled with exitReservations := cancelled.exitReservations.set! token .released }
  have restored : cancelled.exitReservations[token]? = some .restored := by
    simp only [cancelled, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt inside
  have cancellation := cancel_active_direct_saves_snapshot state cleaned token incoming reserved selected snapshot row
    ticket resolved present active tree direct
  refine ⟨final, ?_, ?_⟩
  · simp only [bind, show cancelExitReservation token [] state = .ok () cancelled from cancellation]
    change releaseExitReservation token cancelled = .ok () final
    simp only [releaseExitReservation, ConstructionM.get, bind, restored, ConstructionM.set]
    rfl
  · intro index different
    simp [final, cancelled, cleaned, abandonRowState, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne, Ne.symm different]

#print axioms cancel_leaf_preserves_other_storage

end Goose.Proofs.ConstructionAcceptedExecution
