import Goose.Proofs.ConstructionExecutionOwnershipReservations
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

theorem destinationCurrent_source_bound (state : ConstructionState) (incoming current : DestinationId)
    (resolved : destinationCurrent state incoming = .ok current) : incoming < state.destinations.size := by
  by_cases inside : incoming < state.destinations.size
  · exact inside
  · simp only [destinationCurrent_result, destinationCurrentSteps_succ, if_neg inside] at resolved
    cases resolved

theorem rearmExitReservation_restored (state : ConstructionState)
    (borrowed : BorrowedWaitingExitReservation) (current : DestinationId) (row : PendingDestination)
    (restored : state.exitReservations[borrowed.token]? = some .restored)
    (resolved : destinationCurrent state borrowed.incoming = .ok current)
    (present : state.destinations[current]? = some row) :
    rearmExitReservation borrowed state = .ok ()
      { state with exitReservations := state.exitReservations.set! borrowed.token (.waiting borrowed.incoming) } := by
  simp only [rearmExitReservation, ConstructionM.get, bind, restored, resolved, pure]
  rw [lookupDestination_result]
  simp [present, ConstructionM.set]

theorem rearmExitReservation_not_restored (state : ConstructionState)
    (borrowed : BorrowedWaitingExitReservation)
    (notRestored : state.exitReservations[borrowed.token]? ≠ some .restored) :
    rearmExitReservation borrowed state = .fault .protocol state := by
  cases present : state.exitReservations[borrowed.token]? with
  | none => simp [rearmExitReservation, ConstructionM.get, bind, present, ConstructionM.fail]
  | some reservation =>
      cases reservation <;> simp_all [rearmExitReservation, ConstructionM.get, bind, ConstructionM.fail]

theorem rearmExitReservation_unresolved (state : ConstructionState)
    (borrowed : BorrowedWaitingExitReservation) (reason : ConstructionFault)
    (restored : state.exitReservations[borrowed.token]? = some .restored)
    (unresolved : destinationCurrent state borrowed.incoming = .error reason) :
    rearmExitReservation borrowed state = .fault reason state := by
  simp [rearmExitReservation, ConstructionM.get, bind, restored, unresolved, ConstructionM.fail]

theorem rearmExitReservation_missing (state : ConstructionState)
    (borrowed : BorrowedWaitingExitReservation) (current : DestinationId)
    (restored : state.exitReservations[borrowed.token]? = some .restored)
    (resolved : destinationCurrent state borrowed.incoming = .ok current)
    (missing : state.destinations[current]? = none) :
    rearmExitReservation borrowed state = .fault .destination state := by
  simp only [rearmExitReservation, ConstructionM.get, bind, restored, resolved, pure]
  rw [lookupDestination_result]
  simp [missing]

theorem rearmExitReservation_preserves_construction (state : ConstructionState)
    (borrowed : BorrowedWaitingExitReservation) :
    let final := (rearmExitReservation borrowed state).finalState
    final.storage = state.storage ∧ final.destinations = state.destinations ∧
      final.events = state.events ∧ final.stdout = state.stdout ∧
      final.destinationSuccessors = state.destinationSuccessors ∧
      final.destinationResumptions = state.destinationResumptions ∧
      final.exitReservations.size = state.exitReservations.size := by
  by_cases restored : state.exitReservations[borrowed.token]? = some .restored
  · cases resolved : destinationCurrent state borrowed.incoming with
    | error reason =>
        simp [rearmExitReservation_unresolved state borrowed reason restored resolved, ConstructionResult.finalState]
    | ok current =>
        cases present : state.destinations[current]? with
        | none =>
            simp [rearmExitReservation_missing state borrowed current restored resolved present, ConstructionResult.finalState]
        | some row =>
            simp [rearmExitReservation_restored state borrowed current row restored resolved present, ConstructionResult.finalState]
  · simp [rearmExitReservation_not_restored state borrowed restored, ConstructionResult.finalState]

theorem rearmExitReservation_successors (state : ConstructionState)
    (borrowed : BorrowedWaitingExitReservation) (valid : DestinationSuccessorsValid state) :
    DestinationSuccessorsValid (rearmExitReservation borrowed state).finalState := by
  have frame := rearmExitReservation_preserves_construction state borrowed
  exact destinationSuccessorsValid_extension state _ valid frame.2.2.2.2.1
    (Nat.le_of_eq (congrArg Array.size frame.2.1).symm)

end Goose.Proofs.ConstructionExecutionOwnership
