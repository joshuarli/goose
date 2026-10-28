import Goose.Proofs.ConstructionExitBorrowedNamedRearm

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem lifted_named_cancel (origin : OriginId) (carried : List Nat) (state : ExecutionState)
    (token incoming selected : Nat) (stage : NamedReservationStage) (snapshot : PendingDestination)
    (ticket : state.construction.exitReservations[token]? = some (.active (.named stage) incoming selected snapshot)) :
    liftConstruction origin (cancelExitReservation token carried) state = .ok ()
      { state with construction := { state.construction with
        exitReservations := state.construction.exitReservations.set! token .restored } } := by
  have cancel : cancelExitReservation token carried state.construction = .ok ()
      { state.construction with exitReservations := state.construction.exitReservations.set! token .restored } := by
    simp [cancelExitReservation, ConstructionM.get, ticket, bind, ConstructionM.set]
  simp only [liftConstruction, cancel]

theorem borrowed_named_step (origin : OriginId) (carriers : List Carrier)
    (receipt : BorrowedWaitingExitReservation) (state : ExecutionState)
    (stage : NamedReservationStage) (incoming selected current : Nat) (snapshot row : PendingDestination)
    (ticket : state.construction.exitReservations[receipt.token]? = some (.active (.named stage) incoming selected snapshot))
    (resolved : destinationCurrent state.construction receipt.incoming = .ok current)
    (present : state.construction.destinations[current]? = some row)
    (unretained : (carriers.any fun carrier => match carrier with
      | .pendingNamed actual => actual == receipt.token | _ => false) = false) :
    borrowedExitChannelStep origin carriers receipt state = .ok (ForInStep.yield PUnit.unit)
      { state with construction := { state.construction with
        exitReservations := state.construction.exitReservations.set! receipt.token (.waiting receipt.incoming) } } := by
  let carried := carriers.filterMap fun carrier => match carrier with | Carrier.completed id => some id | _ => none
  let restored := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! receipt.token .restored } }
  let waited := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! receipt.token (.waiting receipt.incoming) } }
  have cancelled := lifted_named_cancel origin carried state receipt.token incoming selected stage snapshot ticket
  have inside := (Array.getElem?_eq_some_iff.mp ticket).1
  have restoredTicket : restored.construction.exitReservations[receipt.token]? = some .restored := by
    simp only [restored, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt inside
  have currentRestored : destinationCurrent restored.construction receipt.incoming = .ok current :=
    (destinationCurrent_congr_tables state.construction restored.construction rfl rfl receipt.incoming).trans resolved
  have rearm : rearmExitReservation receipt restored.construction = .ok () waited.construction := by
    simp only [rearmExitReservation, ConstructionM.get, bind, restoredTicket, currentRestored,
      lookupDestination_result, ConstructionM.set, pure]
    simp [restored, waited, present, Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]
  have liftedRearm : liftConstruction origin (rearmExitReservation receipt) restored = .ok () waited := by
    simp only [liftConstruction, rearm]
    rfl
  unfold borrowedExitChannelStep
  split
  · rename_i retained
    have contradiction : false = true := unretained.symm.trans retained
    cases contradiction
  · change (do
      liftConstruction origin (cancelExitReservation receipt.token carried)
      let currentState ← EvalM.get
      match currentState.construction.exitReservations[receipt.token]? with
      | some .restored => do
        liftConstruction origin (rearmExitReservation receipt)
        pure (ForInStep.yield PUnit.unit)
      | some (.waiting actual) => if actual != receipt.incoming then fault .flow else pure (ForInStep.yield PUnit.unit)
      | some (.active ..) => pure (ForInStep.yield PUnit.unit)
      | _ => fault .flow) state = .ok (ForInStep.yield PUnit.unit) waited
    simp only [bind, cancelled, EvalM.get, pure]
    change (match restored.construction.exitReservations[receipt.token]? with
      | some .restored => fun state => (do liftConstruction origin (rearmExitReservation receipt); pure (ForInStep.yield PUnit.unit)) state
      | some (.waiting actual) => if actual != receipt.incoming then fault .flow else (pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))
      | some (.active ..) => (pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))
      | _ => fault .flow) restored = .ok (ForInStep.yield PUnit.unit) waited
    simp only [restoredTicket, bind, liftedRearm, pure]

#print axioms lifted_named_cancel
#print axioms borrowed_named_step

end Goose.Proofs.ConstructionAcceptedExecution
