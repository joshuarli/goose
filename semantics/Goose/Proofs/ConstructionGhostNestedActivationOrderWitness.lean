import Goose.Proofs.ConstructionGhostNestedActivationOrder

namespace Goose.Proofs.ConstructionGhostNestedActivationOrderWitness
open Goose.Construct Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostResultScope
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionGhostCallHistorical Goose.Proofs.ConstructionGhostNestedActivationOrder
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceTransition

private def implementation : Impl := ⟨"callee", #[], #[], #[], .mk 1 [] none, .unknown⟩
private def context : Context := ⟨0, "callee", [], [], []⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def activationReady : ExecutionState := .initial
private def parent : RuntimeActivation := ⟨1, 0, #[], [], []⟩
private def activated : ExecutionState := { activationReady with nextAct := 1, activations := [parent] }
private def ready : ExecutionState := resultScopeStart parent 0 activated
private def scopedEnvironment : RuntimeActivation := { parent with scopes := [(0, activated.nextScope)] }
private def statement : Stmt := .expr (.call 0 [] 0) 0
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state
private def after : ExecutionState := stepState (execStmt 36 config scopedEnvironment statement ready)
private def visit : StatementInvocation := ⟨0, 0, 36, statement, ready, .ok (.normal .unit) after⟩

theorem nestedActivation_order_witness : ∃ innerResult,
    StatementReplay config scopedEnvironment 37 0 [statement] ready (.ok (.normal .unit) after) [visit] ∧
    CallAllocation config ready innerResult 1 ∧ parent.act < 1 ∧
    evalValue 35 config scopedEnvironment (.call 0 [] 0) ready = callValueResult 0 innerResult := by
  have bound : bindAll parent.act activated.nextScope [] (resultScopeStart parent 0 activated) = .ok () ready := by
    simp [ready, bindAll, bind, pure]
  have head : execStmt 36 config scopedEnvironment statement ready = .ok (.normal .unit) after := by
    simp only [after, stepState, config, implementation, context, scopedEnvironment, statement, ready, parent, activated, activationReady]
    cbv
  have replay : StatementReplay config scopedEnvironment 37 0 [statement] ready (.ok (.normal .unit) after) [visit] :=
    .next head (.done 35 1 after)
  have inner : CallAllocation config ready (invokeCall 34 config scopedEnvironment 0 [] [] 0 ready) 1 := by
    refine ⟨33, scopedEnvironment, 0, [], [], 0, ready, ready, ready, ready, 0, implementation, [], [], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · simp [getImplementation, config, context, bind, pure]
    · rfl
    · simp [prepareCallableChannels, implementation, bind, pure]
    · simp [evalArguments, implementation, pure]
    · simp [refreshCallableChannels, pure]
    · simp [ready, resultScopeStart, activated, activationReady, parent, Goose.Core.maxCallDepth]
    · rfl
  have ordered := reachedActivation_visitBeforeNestedCall (config := config) (id := 1) (activationReady := activationReady)
    (boundReady := ready) (vars := #[]) (channels := []) (pre := []) (scope := 0) bound replay visit (by simp) inner
  refine ⟨_, replay, inner, ordered, ?_⟩
  exact valueCall_source 34 config scopedEnvironment 0 context implementation 0 ready rfl rfl rfl

#print axioms nestedActivation_order_witness
end Goose.Proofs.ConstructionGhostNestedActivationOrderWitness
