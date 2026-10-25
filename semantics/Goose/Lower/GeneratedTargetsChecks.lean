import Goose.Lower.GeneratedBuilder

namespace Goose.Lower.GeneratedTargetsChecks

open Goose.Core Goose.GIR Goose.Lower.Validation

private def entry : LS := ⟨#[⟨[], #[]⟩], #[], some 0, [], #[]⟩

private def futureEdge : LS := ⟨#[⟨[], #[.term (.br 1 [])]⟩], #[], some 0, [], #[]⟩

example : ¬ TargetsBounded futureEdge := by
  intro bounded
  have invalid := bounded 0 ⟨[], #[.term (.br 1 [])]⟩ rfl 1 (by decide)
  change 1 < 1 at invalid
  exact Nat.lt_irrefl 1 invalid

example : ¬ LoopBuilderTargets (some ⟨0, 1, .jump 1⟩) entry := by
  simp [LoopBuilderTargets, entry]

example : futureEdge.DenseDefinitions ∧ LiveBound futureEdge ∧
    ¬ GeneratedBuilderState futureEdge := by
  refine ⟨?_, ?_, ?_⟩
  · simp [futureEdge, LS.DenseDefinitions, LS.defs, BlockB.defs]
  · intro block current
    change some 0 = some block at current
    cases current
    decide
  · intro generated
    have invalid := generated.targets 0 ⟨[], #[.term (.br 1 [])]⟩ rfl 1 (by decide)
    exact Nat.lt_irrefl 1 invalid

example (env : LEnv) (expr : Expr) (before : LS) (bounded : TargetsBounded before) :
    TargetsBounded (lowerExpr expr env before).2 :=
  (generatedTargets_lowerExpr none expr env before _ _ (by apply Prod.ext <;> rfl) bounded trivial).1

example (env : LEnv) (stmt : Stmt) (before : LS) (bounded : TargetsBounded before) :
    TargetsBounded (lowerStmt none stmt env before).2 :=
  (generatedTargets_lowerStmt none stmt env before _ _
    (by apply Prod.ext <;> rfl) bounded trivial).1

end Goose.Lower.GeneratedTargetsChecks
