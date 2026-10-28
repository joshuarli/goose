import Goose.Proofs.ConstructionExitBorrowedRetained
import Goose.Proofs.ConstructionExitNamedCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem borrowed_named_cancel_rearm (carried : List Nat)
    (receipt : BorrowedWaitingExitReservation) (state : ExecutionState)
    (stage : NamedReservationStage) (incoming selected current : Nat) (snapshot row : PendingDestination)
    (ticket : state.construction.exitReservations[receipt.token]? = some (.active (.named stage) incoming selected snapshot))
    (resolved : destinationCurrent state.construction receipt.incoming = .ok current)
    (present : state.construction.destinations[current]? = some row)
    : (do cancelExitReservation receipt.token carried; rearmExitReservation receipt) state.construction =
      .ok () { state.construction with
        exitReservations := state.construction.exitReservations.set! receipt.token (.waiting receipt.incoming) } := by
  let restored := { state.construction with exitReservations := state.construction.exitReservations.set! receipt.token .restored }
  let waited := { state.construction with exitReservations := state.construction.exitReservations.set! receipt.token (.waiting receipt.incoming) }
  have inside := (Array.getElem?_eq_some_iff.mp ticket).1
  have restoredTicket : restored.exitReservations[receipt.token]? = some .restored := by
    simp only [restored, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt inside
  have cancel : cancelExitReservation receipt.token carried state.construction = .ok () restored := by
    simp [cancelExitReservation, ConstructionM.get, ticket, bind, ConstructionM.set, restored]
  have currentRestored : destinationCurrent restored receipt.incoming = .ok current := by
    exact (destinationCurrent_congr_tables state.construction restored rfl rfl receipt.incoming).trans resolved
  have rearm : rearmExitReservation receipt restored = .ok () waited := by
    simp only [rearmExitReservation, ConstructionM.get, bind, restoredTicket, currentRestored,
      lookupDestination_result, ConstructionM.set, pure]
    simp [restored, waited, present, Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]
  simp only [bind, cancel, rearm]
  rfl

#print axioms borrowed_named_cancel_rearm

end Goose.Proofs.ConstructionAcceptedExecution
