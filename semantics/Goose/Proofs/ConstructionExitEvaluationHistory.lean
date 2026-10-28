import Goose.Proofs.ConstructionExitDirectCoverage
import Goose.Proofs.OwnershipEvaluationActions

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

def EvaluationHistoryCoverage (state : ExecutionState) (ambient : OwnershipAmbient)
    (pending : List PendingCarrierFrame) : Prop :=
  ReservationReferencesBounded state.construction ambient ∧
    ∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ pending, .completed id ∈ frame.carriers

theorem initial_evaluationHistoryCoverage : EvaluationHistoryCoverage .initial [] [] := by
  constructor
  · exact initial_reservationReferencesBounded
  · intro id present
    simp [OwnershipAmbient.retained] at present

theorem evaluation_zero_history_coverage (config : EvalConfig) (shape : OwnershipResultShape α)
    (action : EvalM α) (actual : OwnershipEvaluationAction 0 config shape action)
    (state : ExecutionState) (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame)
    (valid : EvaluationHistoryCoverage state ambient pending) :
    EvaluationHistoryCoverage (Goose.Proofs.Exit.stepState (action state)) ambient pending := by
  cases actual <;>
    simpa only [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
      buildExpr, buildElement, evalArguments, invokeCall, enterActivation, execActivationBody,
      execResultBlock, execResultBlockWith, execBlock, execStmts, execStmt, evalPrintArg,
      execWhile, execRange, execEach, loopBody, pushValue, timeout, EvalM.stop,
      Goose.Proofs.Exit.stepState] using valid

theorem completion_setup_evaluationHistoryCoverage (channels : List Channel) (origin : Goose.Core.OriginId)
    (before after : ExecutionState) (planned : List Channel) (tokens : List Nat)
    (ambient : OwnershipAmbient) (carriers : List Goose.Construct.Carrier) (activation : RuntimeActivation)
    (pending : List PendingCarrierFrame) (valid : EvaluationHistoryCoverage before ambient pending)
    (executed : ownershipCompletionSetupAt channels origin before = .ok (planned, tokens) after)
    (activationChannels : activation.channels = planned) :
    EvaluationHistoryCoverage after
      (.callChannels activation carriers :: .completionChannels tokens channels [] :: ambient)
      ({ channels := planned, carriers := carriers } :: pending) := by
  exact completion_setup_history_and_coverage channels origin before after planned tokens ambient carriers activation pending
    valid.1 valid.2 executed activationChannels

#print axioms completion_setup_evaluationHistoryCoverage
#print axioms initial_evaluationHistoryCoverage
#print axioms evaluation_zero_history_coverage

end Goose.Proofs.ConstructionAcceptedExecution
