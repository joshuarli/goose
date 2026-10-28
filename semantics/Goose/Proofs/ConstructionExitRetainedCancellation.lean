import Goose.Proofs.ConstructionExitSuspendedAllocation
import Goose.Proofs.ConstructionExecutionProtocolCurrent
import Goose.Proofs.ConstructionExecutionOwnershipCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem cancelExitReservation_retained_descendant (state : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot : PendingDestination) (carried : List DestinationId)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (retained : carried.any (destinationDescendant state.destinations selected) = true) :
    cancelExitReservation token carried state = .ok () state := by
  simp only [cancelExitReservation, ConstructionM.get, ticket, resolved, bind, pure, retained, ↓reduceIte]

theorem cancelExitReservation_retained_selected (state : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected) :
    cancelExitReservation token [selected] state = .ok () state := by
  have inside := (destinationCurrent_bounds state reserved selected resolved).2
  have self := destinationDescendant_self state selected inside
  dsimp only [destinationDescendant] at self
  simp only [cancelExitReservation, ConstructionM.get, ticket, resolved, bind, pure,
    List.any_cons, self, Bool.true_or, ↓reduceIte]

#print axioms cancelExitReservation_retained_descendant
#print axioms cancelExitReservation_retained_selected

end Goose.Proofs.ConstructionAcceptedExecution
