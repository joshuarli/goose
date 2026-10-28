import Goose.Proofs.ConstructionExitEvaluationHistory
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadata
import Goose.Proofs.ConstructionExecutionProtocolReservationLifecycle

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

def EvaluationHistoryLifecycle (state : ExecutionState) (ambient : OwnershipAmbient)
    (pending : List PendingCarrierFrame) : Prop :=
  ReservationLifecycleInvariant state.construction ∧ EvaluationHistoryCoverage state ambient pending

def PreservesEvaluationHistoryLifecycle (action : EvalM α) (ambient : OwnershipAmbient)
    (pending : List PendingCarrierFrame) : Prop :=
  ∀ state, EvaluationHistoryLifecycle state ambient pending →
    EvaluationHistoryLifecycle (Goose.Proofs.Exit.stepState (action state)) ambient pending

theorem evaluationHistoryLifecycle_query (action : EvalM α) (ambient : OwnershipAmbient)
    (pending : List PendingCarrierFrame) (query : Goose.Proofs.ExitExecution.StateQuery action) :
    PreservesEvaluationHistoryLifecycle action ambient pending := by
  intro state valid
  rw [query state]
  exact valid

theorem evaluationHistoryLifecycle_bind (action : EvalM α) (next : α → EvalM β)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame)
    (first : PreservesEvaluationHistoryLifecycle action ambient pending)
    (following : ∀ value, PreservesEvaluationHistoryLifecycle (next value) ambient pending) :
    PreservesEvaluationHistoryLifecycle (action >>= next) ambient pending := by
  intro state valid
  have firstValid := first state valid
  cases result : action state with
  | ok value after =>
    simp only [result, Goose.Proofs.Exit.stepState] at firstValid
    simpa only [bind, result] using following value after firstValid
  | stop reason after => simpa only [bind, result, Goose.Proofs.Exit.stepState] using firstValid
  | escape target carriers after => simpa only [bind, result, Goose.Proofs.Exit.stepState] using firstValid
  | jump target kind after => simpa only [bind, result, Goose.Proofs.Exit.stepState] using firstValid

theorem evaluationHistoryLifecycle_primitive (origin : OriginId) (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin action) ambient pending := by
  intro state valid
  have metadata := constructionPrimitive_reservation_frame action primitive state.construction valid.1.1
  have lifecycle := reservationLifecyclePrimitives.preserves action primitive state.construction valid.1
  have bounded := reservationReferencesBounded_mono state.construction (action state.construction).finalState ambient
    (by rw [metadata.tickets]; exact Nat.le_refl _) valid.2.1
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

#print axioms evaluationHistoryLifecycle_query
#print axioms evaluationHistoryLifecycle_bind
#print axioms evaluationHistoryLifecycle_primitive

end Goose.Proofs.ConstructionAcceptedExecution
