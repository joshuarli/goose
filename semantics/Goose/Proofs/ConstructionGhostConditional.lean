import Goose.Proofs.ConstructionGhostInvocation

namespace Goose.Proofs.ConstructionGhostConditional
open Goose.Construct Goose.Proofs.ConstructionGhostInvocation

def conditionalContinuation (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (yes no : Block) (source : ExecutionStep Value) : ExecutionStep Value :=
  match source with
  | .ok value state => (do
      let selected ← expectBool value
      let flow ← if selected then execBlock fuel config environment [] [] yes
        else execBlock fuel config environment [] [] no
      match flow with
      | .normal value => pure value
      | _ => fault .flow) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem conditional_condition_ghost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (path : List Nat) (condition : Expr) (yes no : Block)
    (origin : Goose.Core.OriginId) (before : ExecutionState) :
    EvaluationTree config environment fuel (path ++ [0]) condition before
      (evalValue fuel config environment condition before) ∧
    evalValue (fuel + 1) config environment (.ifE condition yes no origin) before =
      conditionalContinuation fuel config environment yes no
        (evalValue fuel config environment condition before) := by
  refine ⟨evaluationTree_exists fuel config environment _ _ _, ?_⟩
  simp only [evalValue, bind, conditionalContinuation]
  cases evalValue fuel config environment condition before <;> rfl

private def conditionalWitness : Expr :=
  .ifE (.blockE (.mk 0 [.print [.text "condition"] 0] (some (.bool true))) 0)
    (.mk 1 [.print [.text "selected"] 0] (some (.lit .i64 7)))
    (.mk 2 [.print [.text "skipped"] 0] (some (.lit .i64 8))) 0

private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩

private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem conditionalWitness_sideEffect :
    ∃ state, evalValue 40 witnessConfig witnessEnvironment conditionalWitness .initial =
      .ok (.int .i64 7) state ∧
      state.construction.stdout.data.toList =
        [99, 111, 110, 100, 105, 116, 105, 111, 110, 10, 115, 101, 108, 101, 99, 116, 101, 100, 10] := by
  refine ⟨stepState (evalValue 40 witnessConfig witnessEnvironment conditionalWitness .initial), ?_, ?_⟩ <;>
    unfold witnessConfig witnessEnvironment conditionalWitness stepState <;> cbv

#print axioms conditionalWitness_sideEffect
#print axioms conditional_condition_ghost
end Goose.Proofs.ConstructionGhostConditional
