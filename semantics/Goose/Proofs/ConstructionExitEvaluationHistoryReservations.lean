import Goose.Proofs.ConstructionExitEvaluationHistoryPrimitives
import Goose.Proofs.ConstructionExecutionProtocolReservationPrimitives

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem evaluationHistoryLifecycle_reservation (origin : OriginId) (action : ConstructionM α)
    (primitive : ConstructionReservationPrimitive action) (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame)
    (size : ∀ state, ReservationLifecycleInvariant state →
      state.exitReservations.size ≤ (action state).finalState.exitReservations.size) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin action) ambient pending := by
  intro state valid
  have lifecycle := reservationLifecycleReservationPrimitives.preserves action primitive state.construction valid.1
  have bounded := reservationReferencesBounded_mono state.construction (action state.construction).finalState ambient
    (size state.construction valid.1) valid.2.1
  have coverage := valid.2.2
  cases result : action state.construction with
  | ok value construction =>
    simp only [result, ConstructionResult.finalState] at lifecycle bounded
    simpa only [liftConstruction, result, Goose.Proofs.Exit.stepState, EvaluationHistoryLifecycle,
      EvaluationHistoryCoverage] using And.intro lifecycle (And.intro bounded coverage)
  | fault kind construction =>
    simp only [result, ConstructionResult.finalState] at lifecycle bounded
    cases kind <;> simpa only [liftConstruction, result, Goose.Proofs.Exit.stepState, EvaluationHistoryLifecycle,
      EvaluationHistoryCoverage] using And.intro lifecycle (And.intro bounded coverage)

theorem evaluationHistoryLifecycle_wait (origin : OriginId) (id : Nat)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (waitExitDestination id)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.waitExitDestination id) ambient pending
  intro state valid
  simp [waitExitDestination, ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.finalState]

theorem evaluationHistoryLifecycle_release (origin : OriginId) (token : Nat)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (releaseExitReservation token)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.releaseExitReservation token) ambient pending
  intro state valid
  simp only [releaseExitReservation, ConstructionM.get, bind]
  cases ticket : state.exitReservations[token]? with
  | none => simp [ticket, ConstructionM.fail, ConstructionResult.finalState]
  | some status =>
    cases status <;> simp [ticket, ConstructionM.set, ConstructionM.fail, pure, bind, ConstructionResult.finalState]

#print axioms evaluationHistoryLifecycle_reservation
#print axioms evaluationHistoryLifecycle_wait
#print axioms evaluationHistoryLifecycle_release

end Goose.Proofs.ConstructionAcceptedExecution
