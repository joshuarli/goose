import Goose.Proofs.ConstructionExitDirectResumption
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataTree

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem cancel_active_direct_preserves_older (state cleaned : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot selectedRow : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (selectedFound : state.destinations[selected]? = some selectedRow) (active : activeRow selectedRow = true)
    (tree : abandonTree selected state = .ok () cleaned) (direct : reserved = snapshot.capability.id)
    (lifecycle : ReservationLifecycleInvariant state) :
    ∃ final, (do cancelExitReservation token []; releaseExitReservation token) state = .ok () final ∧
      (∀ index, index < selected → final.destinations[index]? = state.destinations[index]?) ∧
      (∀ other, other ≠ token → final.exitReservations[other]? = state.exitReservations[other]?) := by
  have frame := abandonTree_reservation_frame selected state lifecycle.1
  have tickets : cleaned.exitReservations = state.exitReservations := by
    simpa only [tree, ConstructionResult.finalState] using frame.tickets
  let cancelled := { cleaned with
    destinationResumptions := (selected, snapshot) :: cleaned.destinationResumptions
    exitReservations := cleaned.exitReservations.set! token .restored }
  let final := { cancelled with exitReservations := cancelled.exitReservations.set! token .released }
  have inside : token < cleaned.exitReservations.size := by
    rw [tickets]
    exact (Array.getElem?_eq_some_iff.mp ticket).1
  have restored : cancelled.exitReservations[token]? = some .restored := by
    simp only [cancelled, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt inside
  refine ⟨final, ?_, ?_, ?_⟩
  · have cancel := cancel_active_direct_saves_snapshot state cleaned token incoming reserved selected snapshot selectedRow
      ticket resolved selectedFound active tree direct
    change (do cancelExitReservation token []; releaseExitReservation token) state = .ok () final
    simp only [bind, show cancelExitReservation token [] state = .ok () cancelled from cancel]
    change releaseExitReservation token cancelled = .ok () final
    simp only [releaseExitReservation, ConstructionM.get, bind, restored, ConstructionM.set]
    rfl
  · intro index earlier
    exact abandonTree_success_earlier_row state cleaned selected index lifecycle.1.2.1 lifecycle.1.2.2.2 earlier tree
  · intro other different
    simp [final, cancelled, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm different, tickets]

#print axioms cancel_active_direct_preserves_older

end Goose.Proofs.ConstructionAcceptedExecution
