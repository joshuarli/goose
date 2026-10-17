import Goose.Lower.Validation.SourceStatementTypingControl

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

theorem tyStmt_expr_children {env output : TEnv} {expr : Expr} {origin : OriginId}
    {scope start finish : Nat}
    (source : Core.tyStmt env scope (.expr expr origin) start = .ok (output, finish)) :
    ∃ type, Core.tyExpr env expr start = .ok (type, finish) ∧ output = env := by
  simp only [Core.tyStmt] at source
  inv at source
  obtain ⟨_, type, childFinish, child, outputEq, finishEq⟩ := source
  subst finish
  exact ⟨type, child, outputEq⟩

theorem tyStmt_assert_children {env output : TEnv} {expr : Expr} {origin : OriginId}
    {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assertS expr origin) start = .ok (output, finish)) :
    Core.tyExpr env expr start = .ok (.bool, finish) ∧ output = env := by
  simp only [Core.tyStmt] at source
  inv at source
  obtain ⟨_, type, childFinish, child, typeEq, outputEq, finishEq⟩ := source
  subst type
  subst finish
  exact ⟨child, outputEq⟩

theorem tyStmt_exit_children {env output : TEnv} {expr : Expr} {origin : OriginId}
    {scope start finish : Nat}
    (source : Core.tyStmt env scope (.exit expr origin) start = .ok (output, finish)) :
    ∃ integer, Core.tyExpr env expr start = .ok (.int integer, finish) ∧ output = env := by
  simp only [Core.tyStmt] at source
  inv at source
  obtain ⟨_, type, childFinish, child, integer, typeEq, outputEq, finishEq⟩ := source
  subst type
  subst finish
  exact ⟨integer, child, outputEq⟩

theorem tyStmt_return_children {env output : TEnv} {expr : Expr} {origin : OriginId}
    {scope start finish : Nat}
    (source : Core.tyStmt env scope (.ret (some expr) origin) start = .ok (output, finish)) :
    ∃ expected actual impl,
      env.inExpr = false ∧ env.impl = some impl ∧ impl.results.toList = [expected] ∧
      Core.tyExpr env expr start = .ok (actual, finish) ∧
      actual.passableTo expected = true ∧ output = env := by
  simp only [Core.tyStmt] at source
  inv at source
  obtain ⟨_, expected, childStart, returnChecked, actual, childFinish,
    child, passable, outputEq, finishEq⟩ := source
  obtain ⟨same, notInExpr, impl, implAt, results⟩ := retTy_ok _ _ _ returnChecked
  change childStart = start at same
  subst childStart
  subst finish
  exact ⟨expected, actual, impl, notInExpr, implAt, results, child, passable, outputEq⟩

theorem tyStmt_returnUnit_facts {env output : TEnv} {origin : OriginId}
    {scope start finish : Nat}
    (source : Core.tyStmt env scope (.ret none origin) start = .ok (output, finish)) :
    env.inExpr = false ∧ (∃ impl, env.impl = some impl ∧ impl.results.toList = []) ∧
      output = env ∧ finish = start := by
  simp only [Core.tyStmt] at source
  inv at source
  obtain ⟨_, returnFinish, returnChecked, outputEq, finishEq⟩ := source
  obtain ⟨same, notInExpr, impl, implAt, results⟩ := retUnit_ok _ _ _ returnChecked
  exact ⟨notInExpr, ⟨impl, implAt, results⟩, outputEq, finishEq.trans same⟩

theorem tyStmt_break_facts {env output : TEnv} {origin : OriginId}
    {scope start finish : Nat}
    (source : Core.tyStmt env scope (.brk origin) start = .ok (output, finish)) :
    env.loops ≠ 0 ∧ output = env ∧ finish = start := by
  simp only [Core.tyStmt] at source
  inv at source
  obtain ⟨_, positive, outputEq, finishEq⟩ := source
  exact ⟨positive, outputEq, finishEq⟩

theorem tyStmt_continue_facts {env output : TEnv} {origin : OriginId}
    {scope start finish : Nat}
    (source : Core.tyStmt env scope (.cont origin) start = .ok (output, finish)) :
    env.loops ≠ 0 ∧ output = env ∧ finish = start := by
  simp only [Core.tyStmt] at source
  inv at source
  obtain ⟨_, positive, outputEq, finishEq⟩ := source
  exact ⟨positive, outputEq, finishEq⟩

theorem tyStmt_abort_facts {env output : TEnv} {message : String} {origin : OriginId}
    {scope start finish : Nat}
    (source : Core.tyStmt env scope (.abort message origin) start = .ok (output, finish)) :
    output = env ∧ finish = start := by
  simp only [Core.tyStmt] at source
  inv at source
  exact source.2

theorem tyStmt_print_children {env output : TEnv} {args : List PrintArg} {origin : OriginId}
    {scope start finish : Nat}
    (source : Core.tyStmt env scope (.print args origin) start = .ok (output, finish)) :
    Core.tyPrintArgs env args start = .ok ((), finish) ∧ output = env := by
  simp only [Core.tyStmt] at source
  inv at source
  obtain ⟨_, printFinish, checked, outputEq, finishEq⟩ := source
  subst finish
  exact ⟨checked, outputEq⟩

theorem tyPrintArgs_expr_children {env : TEnv} {args : List PrintArg} {expr : Expr}
    {start finish : Nat} (source : Core.tyPrintArgs env args start = .ok ((), finish))
    (member : PrintArg.expr expr ∈ args) :
    ∃ type childStart childFinish, Core.tyExpr env expr childStart = .ok (type, childFinish) ∧
      (type = .bool ∨ ∃ integer, type = .int integer) := by
  induction args generalizing start with
  | nil => cases member
  | cons arg rest ih =>
    cases arg with
    | text text =>
      simp only [List.mem_cons, reduceCtorEq, false_or] at member
      exact ih source member
    | expr first =>
      simp only [Core.tyPrintArgs] at source
      obtain ⟨type, next, child, source⟩ := (st_bind_ok _ _ _ _).mp source
      cases type <;> simp only at source
      all_goals try { inv at source }
      all_goals
        rcases List.mem_cons.mp member with equal | remaining
        · cases equal
          refine ⟨_, start, next, child, ?_⟩
          simp
        · exact ih source remaining

end Goose.Lower.Validation
