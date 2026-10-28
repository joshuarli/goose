import Goose.Proofs.ConstructionExitEvaluationHistoryOutcome
import Goose.Proofs.ConstructionAcceptedNumericComplete
import Goose.Proofs.ExitExecutionLiveCarriers

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

private theorem numeric_register_produce {expression : Expr} (form : AcceptedNumericExpression expression)
    (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (ty : Ty) (state : ExecutionState) :
    evalProduce (fuel + 1) config environment [.register ty] expression state =
      (do let value ← evalValue fuel config environment expression; pure [Goose.Construct.Carrier.register value]) state := by
  cases form with
  | scalar form =>
    cases form with
    | scalar form =>
      cases form <;> simp only [evalProduce, List.mapM_cons, List.mapM_nil, selectCompletionChannel, bind, pure]
    | not form => simp only [evalProduce, List.mapM_cons, List.mapM_nil, selectCompletionChannel, bind, pure]
  | unary operation origin form => simp only [evalProduce, List.mapM_cons, List.mapM_nil, selectCompletionChannel, bind, pure]
  | conversion kind target origin form => simp only [evalProduce, List.mapM_cons, List.mapM_nil, selectCompletionChannel, bind, pure]

theorem accepted_numeric_register_outcomes {expression : Expr} (form : AcceptedNumericExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (history : EvaluationHistoryCoverage state ambient pending) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    let action := evalProduce (fuel + 1) config frame.interpretation.environment [.register ty] expression
    EvaluationHistoryLifecycleOutcome .carriers [.register ty] ambient pending (action state) ∧
      Goose.Proofs.Exit.stepState (action state) = state ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState (action state)) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState (action state)) types ∧
      (∀ carriers after, action state = .ok carriers after →
        ∃ value, carriers = [.register value] ∧ after = state ∧
          AcceptedValue config.layout types frame.interpretation after ty roots value ∧
          CarriersLandingReady after [.register ty] carriers ∧
          (∀ carrier ∈ carriers, CarrierResultBacking config.layout after carrier) ∧
          landCarriersInto 0 [.register ty] carriers after = .ok () after) := by
  have historyValid : EvaluationHistoryLifecycle state ambient pending := ⟨world.ownership.source.structural.1.1, history⟩
  have outcome := evaluator_history_outcome (fuel + 1) config .carriers _
    (.produce frame.interpretation.environment [.register ty] expression) state ambient pending [.register ty] historyValid
  have valueResult := evalValue_checked_numeric_complete form fuel config accepted frame state ambient types live regions pending
    world source ty roots typingAfter rootsAfter checked
  have equation := numeric_register_produce form fuel config frame.interpretation.environment ty state
  have stateUnchanged : Goose.Proofs.Exit.stepState
      (evalProduce (fuel + 1) config frame.interpretation.environment [.register ty] expression state) = state := by
    rw [equation]
    cases evaluated : evalValue fuel config frame.interpretation.environment expression state <;>
      simp only [bind, evaluated, pure, Goose.Proofs.Exit.stepState] <;>
      simpa only [evaluated, Goose.Proofs.Exit.stepState] using valueResult.1
  refine ⟨outcome, stateUnchanged, ?_, ?_, ?_⟩
  · simpa only [stateUnchanged] using world
  · simpa only [stateUnchanged] using source
  · intro carriers after success
    rw [equation] at success
    cases evaluated : evalValue fuel config frame.interpretation.environment expression state with
    | stop reason final | escape target carried final | jump target kind final =>
      simp only [bind, evaluated] at success
      cases success
    | ok value final =>
      have acceptedValue := valueResult.2.1 value final evaluated
      have unchanged : final = state := by
        simpa only [evaluated, Goose.Proofs.Exit.stepState] using valueResult.1
      subst final
      simp only [bind, evaluated, pure, ExecutionStep.ok.injEq] at success
      obtain ⟨rfl, rfl⟩ := success
      refine ⟨value, rfl, rfl, acceptedValue, ?_, ?_, ?_⟩
      · refine ⟨rfl, ?_⟩
        intro channel carrier member
        simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
        obtain ⟨rfl, rfl⟩ := member
        exact .register _ _
      · intro carrier member
        simp only [List.mem_singleton] at member
        subst carrier
        exact .register _ acceptedValue.backed
      · simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil, bind, pure]
#print axioms accepted_numeric_register_outcomes

end Goose.Proofs.ConstructionAcceptedExecution
