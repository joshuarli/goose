import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

theorem tyStmt_tables {env after : TEnv} {scope start finish : Nat} (stmt : Stmt)
    (typed : tyStmt env scope stmt start = .ok (after, finish)) :
    after.mod = env.mod ∧ after.vars = env.vars ∧ after.impl = env.impl := by
  cases stmt
  case' resize owner size fill origin => cases fill
  case' ifS condition thenBlock otherwise origin => cases otherwise
  case' ret value origin => cases value
  all_goals simp only [tyStmt] at typed
  all_goals
    repeat' first
    | (subst after; exact ⟨rfl, rfl, rfl⟩)
    | contradiction
    | (simp only [chk, false_and, and_false, exists_false, exists_const, or_false, false_or,
        true_and, Prod.mk.injEq, Prod.exists, and_assoc, exists_eq_left, exists_and_left] at typed)
    | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
    | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
    | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
    | (split at typed)

theorem tyStmts_tables {env after : TEnv} {scope start finish : Nat} (stmts : List Stmt)
    (typed : tyStmts env scope stmts start = .ok (after, finish)) :
    after.mod = env.mod ∧ after.vars = env.vars ∧ after.impl = env.impl := by
  induction stmts generalizing env start with
  | nil =>
    have pair := (st_pure_ok _ _ _).mp typed
    have same : after = env := congrArg Prod.fst pair
    subst after
    exact ⟨rfl, rfl, rfl⟩
  | cons stmt rest inductionHypothesis =>
    simp only [tyStmts] at typed
    obtain ⟨mid, next, first, remaining⟩ := (st_bind_ok _ _ _ _).mp typed
    have head := tyStmt_tables stmt first
    have tail := inductionHypothesis remaining
    exact ⟨tail.1.trans head.1, tail.2.1.trans head.2.1, tail.2.2.trans head.2.2⟩

theorem declarePre_tables {env after : TEnv} {scope start finish : Nat} (pre : List (VarId × Ty))
    (typed : declarePre env scope pre start = .ok (after, finish)) :
    after.mod = env.mod ∧ after.vars = env.vars ∧ after.impl = env.impl := by
  induction pre generalizing env start with
  | nil =>
    have pair := (st_pure_ok _ _ _).mp typed
    have same : after = env := congrArg Prod.fst pair
    subst after
    exact ⟨rfl, rfl, rfl⟩
  | cons first rest inductionHypothesis =>
    obtain ⟨varId, ty⟩ := first
    simp only [declarePre] at typed
    obtain ⟨localVar, next, _, typed⟩ := (st_bind_ok _ _ _ _).mp typed
    by_cases equal : (localVar.ty == ty) = true
    · simp only [equal, ite_true] at typed
      exact inductionHypothesis (env := { env with visible := varId :: env.visible }) typed
    · simp [equal, chk] at typed

theorem tyStmts_lowerEnv {env after : TEnv} {scope start finish : Nat} {stmts : List Stmt}
    (typed : tyStmts env scope stmts start = .ok (after, finish)) (results : List Ty) :
    lowerEnv after.mod after.vars results = lowerEnv env.mod env.vars results := by
  have tables := tyStmts_tables stmts typed
  rw [tables.1, tables.2.1]

theorem declarePre_lowerEnv {env after : TEnv} {scope start finish : Nat} {pre : List (VarId × Ty)}
    (typed : declarePre env scope pre start = .ok (after, finish)) (results : List Ty) :
    lowerEnv after.mod after.vars results = lowerEnv env.mod env.vars results := by
  have tables := declarePre_tables pre typed
  rw [tables.1, tables.2.1]

end Goose.Lower.Validation
