import Goose.Lower.Validation.SourceEnvironment

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound

theorem source_statement_inExpr {env after : TEnv} (statement : Stmt) {scope start finish : Nat}
    (typed : tyStmt env scope statement start = .ok (after, finish)) :
    after.inExpr = env.inExpr := by
  cases statement
  case' resize owner size fill origin => cases fill
  case' ifS condition yes no origin => cases no
  case' ret value origin => cases value
  all_goals simp only [tyStmt] at typed
  all_goals try inv at typed
  all_goals
    repeat' first
      | contradiction
      | rfl
      | (subst after; rfl)
      | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
      | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
      | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
      | (split at typed <;> try inv at typed)

theorem source_statements_inExpr {env after : TEnv} (statements : List Stmt) {scope start finish : Nat}
    (typed : tyStmts env scope statements start = .ok (after, finish)) :
    after.inExpr = env.inExpr := by
  induction statements generalizing env start with
  | nil =>
    have same := (st_pure_ok _ _ _).mp typed
    exact congrArg TEnv.inExpr (congrArg Prod.fst same)
  | cons statement rest ih =>
    obtain ⟨middle, counter, first, remaining⟩ := (st_bind_ok _ _ _ _).mp typed
    exact (ih remaining).trans (source_statement_inExpr statement first)

#print axioms source_statement_inExpr
#print axioms source_statements_inExpr

end Goose.Lower.Validation.SummaryPreservation
