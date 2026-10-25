import Goose.Construct.Destination

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

theorem releaseExitReservation_active (state : ConstructionState) (token : ExitReservationId)
    (role : ExitReservationRole) (incoming selected : DestinationId) (snapshot : PendingDestination)
    (present : state.exitReservations[token]? = some (.active role incoming selected snapshot)) :
    releaseExitReservation token state = .ok ()
      { state with exitReservations := state.exitReservations.set! token .released } := by
  simp [releaseExitReservation, present, ConstructionM.get, ConstructionM.set, bind]

theorem releaseExitReservation_waiting (state : ConstructionState) (token : ExitReservationId)
    (incoming : DestinationId)
    (present : state.exitReservations[token]? = some (.waiting incoming)) :
    releaseExitReservation token state = .ok ()
      { state with exitReservations := state.exitReservations.set! token .released } := by
  simp [releaseExitReservation, present, ConstructionM.get, ConstructionM.set, bind]

theorem releaseExitReservation_restored (state : ConstructionState) (token : ExitReservationId)
    (present : state.exitReservations[token]? = some .restored) :
    releaseExitReservation token state = .ok ()
      { state with exitReservations := state.exitReservations.set! token .released } := by
  simp [releaseExitReservation, present, ConstructionM.get, ConstructionM.set, bind]

theorem releaseExitReservation_released_faults (state : ConstructionState) (token : ExitReservationId)
    (present : state.exitReservations[token]? = some .released) :
    releaseExitReservation token state = .fault .protocol state := by
  simp [releaseExitReservation, present, ConstructionM.get, ConstructionM.fail, bind]

theorem releaseExitReservation_absent_faults (state : ConstructionState) (token : ExitReservationId)
    (present : state.exitReservations[token]? = none) :
    releaseExitReservation token state = .fault .protocol state := by
  simp [releaseExitReservation, present, ConstructionM.get, ConstructionM.fail, bind]

theorem releaseExitReservation_preserves_construction (state : ConstructionState)
    (token : ExitReservationId) :
    let final := (releaseExitReservation token state).finalState
    final.storage = state.storage ∧ final.destinations = state.destinations ∧
      final.events = state.events ∧ final.stdout = state.stdout ∧
      final.destinationSuccessors = state.destinationSuccessors ∧
      final.destinationResumptions = state.destinationResumptions ∧
      final.exitReservations.size = state.exitReservations.size := by
  cases present : state.exitReservations[token]? with
  | none => simp [releaseExitReservation_absent_faults state token present, ConstructionResult.finalState]
  | some reservation =>
      cases reservation with
      | active role incoming selected snapshot =>
          simp [releaseExitReservation_active state token role incoming selected snapshot present,
            ConstructionResult.finalState]
      | waiting incoming =>
          simp [releaseExitReservation_waiting state token incoming present, ConstructionResult.finalState]
      | restored =>
          simp [releaseExitReservation_restored state token present, ConstructionResult.finalState]
      | released =>
          simp [releaseExitReservation_released_faults state token present, ConstructionResult.finalState]

theorem cancelExitReservation_waiting (state : ConstructionState) (token : ExitReservationId)
    (incoming : DestinationId) (carried : List DestinationId)
    (present : state.exitReservations[token]? = some (.waiting incoming)) :
    cancelExitReservation token carried state = .ok () state := by
  simp [cancelExitReservation, present, ConstructionM.get, bind, pure]

theorem cancelExitReservation_restored (state : ConstructionState) (token : ExitReservationId)
    (carried : List DestinationId) (present : state.exitReservations[token]? = some .restored) :
    cancelExitReservation token carried state = .ok () state := by
  simp [cancelExitReservation, present, ConstructionM.get, bind, pure]

theorem cancelExitReservation_released_faults (state : ConstructionState) (token : ExitReservationId)
    (carried : List DestinationId) (present : state.exitReservations[token]? = some .released) :
    cancelExitReservation token carried state = .fault .protocol state := by
  simp [cancelExitReservation, present, ConstructionM.get, ConstructionM.fail, bind]

end Goose.Proofs.ConstructionExecutionOwnership
