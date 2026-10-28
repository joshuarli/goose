import Goose.Proofs.ConstructionExitEvaluationHistoryAll
import Goose.Proofs.ConstructionExitEvaluationHistoryFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

def EvaluationHistoryLifecycleOutcome (shape : OwnershipResultShape α) (channels : List Channel)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) : ExecutionStep α → Prop
  | .ok value state =>
      let carriers := shape.retainedCarriers value
      EvaluationHistoryLifecycle state (.returned carriers :: ambient)
        ({ channels := channels, carriers := carriers } :: pending)
  | .stop _ state => EvaluationHistoryLifecycle state ambient pending
  | .escape _ carriers state =>
      EvaluationHistoryLifecycle state (.returned carriers :: ambient)
        ({ channels := channels, carriers := carriers } :: pending)
  | .jump _ (.breakValue carriers) state =>
      EvaluationHistoryLifecycle state (.returned carriers :: ambient)
        ({ channels := channels, carriers := carriers } :: pending)
  | .jump _ .continueLoop state => EvaluationHistoryLifecycle state ambient pending

theorem evaluationHistoryLifecycle_returned (state : ExecutionState) (ambient : OwnershipAmbient)
    (pending : List PendingCarrierFrame) (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (valid : EvaluationHistoryLifecycle state ambient pending) :
    EvaluationHistoryLifecycle state (.returned carriers :: ambient)
      ({ channels := channels, carriers := carriers } :: pending) :=
  ⟨valid.1, evaluationHistoryCoverage_returned state ambient pending channels carriers valid.2⟩

theorem evaluator_history_outcome (fuel : Nat) (config : EvalConfig) (shape : OwnershipResultShape α)
    (action : EvalM α) (actual : OwnershipEvaluationAction fuel config shape action)
    (state : ExecutionState) (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame)
    (channels : List Channel) (valid : EvaluationHistoryLifecycle state ambient pending) :
    EvaluationHistoryLifecycleOutcome shape channels ambient pending (action state) := by
  have fixed := evaluator_fixed_history_coverage fuel config shape action actual state ambient pending valid
  cases result : action state with
  | ok value after =>
    simp only [result, Goose.Proofs.Exit.stepState] at fixed
    simpa only [result, EvaluationHistoryLifecycleOutcome] using
      evaluationHistoryLifecycle_returned after ambient pending channels (shape.retainedCarriers value) fixed
  | stop reason after =>
    simpa only [result, EvaluationHistoryLifecycleOutcome, Goose.Proofs.Exit.stepState] using fixed
  | escape target carriers after =>
    simp only [result, Goose.Proofs.Exit.stepState] at fixed
    simpa only [result, EvaluationHistoryLifecycleOutcome] using
      evaluationHistoryLifecycle_returned after ambient pending channels carriers fixed
  | jump target kind after =>
    simp only [result, Goose.Proofs.Exit.stepState] at fixed
    cases kind with
    | breakValue carriers =>
      simpa only [result, EvaluationHistoryLifecycleOutcome] using
        evaluationHistoryLifecycle_returned after ambient pending channels carriers fixed
    | continueLoop => simpa only [result, EvaluationHistoryLifecycleOutcome] using fixed

#print axioms evaluator_history_outcome
#print axioms evaluationHistoryLifecycle_returned

end Goose.Proofs.ConstructionAcceptedExecution
