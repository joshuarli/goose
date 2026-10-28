import Goose.Proofs.ConstructionGhostInvocation

namespace Goose.Proofs.ConstructionGhostMaterialization
open Goose.Construct Goose.Proofs.ConstructionGhostInvocation

def materializationContinuation (source : ExecutionStep Value) : ExecutionStep (Option (Array Value)) :=
  match source with
  | .ok (.fixed values) state => .ok (some values) state
  | .ok _ state => .stop (.fault .shape) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem materializeProducer_none (fuel : Nat) (declarations : DeclarationEnv)
    (expression : Expr) (evaluate : EvalM Value) (before : ExecutionState)
    (unknown : ordinaryProducerCount? fuel declarations expression = none) :
    materializeProducer fuel declarations expression evaluate before = .ok none before := by
  simp [materializeProducer, unknown, pure]

theorem materializeProducer_source_ghost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (path : List Nat) (expression : Expr) (before : ExecutionState)
    (count : Nat)
    (known : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count) :
    EvaluationTree config environment fuel (path ++ [0]) expression before
      (evalValue fuel config environment expression before) ∧
    materializeProducer fuel ⟨config.module, environment.vars⟩ expression
      (evalValue fuel config environment expression) before =
      materializationContinuation (evalValue fuel config environment expression before) := by
  refine ⟨evaluationTree_exists fuel config environment _ _ _, ?_⟩
  simp only [materializeProducer, known, bind, materializationContinuation]
  cases evalValue fuel config environment expression before with
  | ok value state => cases value <;> rfl
  | stop | escape | jump => rfl

private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def witnessExpression : Expr := .blockE
  (.mk 0 [.print [.text "once"] 0]
    (some (.arrLit (.arr (.int .i64) 2) [.lit .i64 7, .lit .i64 8] 0))) 0
private def witnessRun : EvalM (Option (Array Value)) :=
  materializeProducer 40 ⟨witnessConfig.module, witnessEnvironment.vars⟩ witnessExpression
    (evalValue 40 witnessConfig witnessEnvironment witnessExpression)
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem materializationWitness_sideEffect :
    ordinaryProducerCount? 40 ⟨witnessConfig.module, witnessEnvironment.vars⟩ witnessExpression = some 2 ∧
    ∃ state, witnessRun .initial = .ok (some #[.int .i64 7, .int .i64 8]) state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  constructor
  · unfold witnessConfig witnessEnvironment witnessExpression; cbv
  · refine ⟨stepState (witnessRun .initial), ?_, ?_⟩ <;>
      unfold witnessRun witnessConfig witnessEnvironment witnessExpression stepState <;> cbv

#print axioms materializationWitness_sideEffect
#print axioms materializeProducer_none
#print axioms materializeProducer_source_ghost
end Goose.Proofs.ConstructionGhostMaterialization
