import Goose.Lower.Validation.SourceStatementTypingTransfers
import Goose.Lower.Validation.SourceEnvironment

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

theorem tyStmts_cons_children {env output : TEnv} {stmt : Stmt} {rest : List Stmt}
    {scope start finish : Nat}
    (source : Core.tyStmts env scope (stmt :: rest) start = .ok (output, finish)) :
    ∃ middle next, Core.tyStmt env scope stmt start = .ok (middle, next) ∧
      Core.tyStmts middle scope rest next = .ok (output, finish) := by
  exact (st_bind_ok _ _ _ _).mp source

theorem tyBlock_checked_children {env : TEnv} {pre : List (VarId × Ty)}
    {scope : Nat} {stmts : List Stmt} {value : Option Expr} {type : Ty} {start finish : Nat}
    (source : Core.tyBlock env pre (.mk scope stmts value) start = .ok (type, finish)) :
    scope ∉ env.scopes ∧ ∃ declared output statementStart valueStart,
      declarePre { env with scopes := scope :: env.scopes } scope pre start = .ok (declared, statementStart) ∧
      Core.tyStmts declared scope stmts statementStart = .ok (output, valueStart) ∧
      (match value with
       | none => type = .unit ∧ finish = valueStart
       | some expr => Core.tyExpr output expr valueStart = .ok (type, finish)) := by
  unfold Core.tyBlock at source
  by_cases nested : scope ∈ env.scopes
  · simp [nested, chk] at source
  · simp only [List.contains_iff_mem, nested, ite_false] at source
    obtain ⟨declared, statementStart, declaration, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨output, valueStart, statements, source⟩ := (st_bind_ok _ _ _ _).mp source
    refine ⟨nested, declared, output, statementStart, valueStart, declaration, statements, ?_⟩
    cases value with
    | none => simpa only [Prod.mk.injEq] using (st_pure_ok _ _ _).mp source
    | some expr => exact source

theorem tyStmts_member_children {env output : TEnv} {stmts : List Stmt} {stmt : Stmt}
    {scope start finish : Nat}
    (source : Core.tyStmts env scope stmts start = .ok (output, finish)) (member : stmt ∈ stmts) :
    ∃ before after childStart childFinish,
      Core.tyStmt before scope stmt childStart = .ok (after, childFinish) ∧
      before.mod = env.mod ∧ before.vars = env.vars ∧ before.impl = env.impl := by
  induction stmts generalizing env start with
  | nil => cases member
  | cons first rest ih =>
    obtain ⟨middle, next, firstTyped, remaining⟩ := tyStmts_cons_children source
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact ⟨env, middle, start, next, firstTyped, rfl, rfl, rfl⟩
    · obtain ⟨before, after, childStart, childFinish, child, moduleEq, varsEq, implEq⟩ := ih remaining member
      have tables := tyStmt_tables first firstTyped
      exact ⟨before, after, childStart, childFinish, child,
        moduleEq.trans tables.1, varsEq.trans tables.2.1, implEq.trans tables.2.2⟩

theorem declarePre_cons_children {env output : TEnv} {x : VarId} {type : Ty}
    {rest : List (VarId × Ty)} {scope start finish : Nat}
    (source : declarePre env scope ((x, type) :: rest) start = .ok (output, finish)) :
    ∃ localVar next, declare env x scope start = .ok (localVar, next) ∧ localVar.ty = type ∧
      declarePre { env with visible := x :: env.visible } scope rest next = .ok (output, finish) := by
  simp only [declarePre] at source
  obtain ⟨localVar, next, declared, source⟩ := (st_bind_ok _ _ _ _).mp source
  by_cases equal : (localVar.ty == type) = true
  · simp only [equal, ite_true] at source
    exact ⟨localVar, next, declared, beq_iff_eq.mp equal, source⟩
  · simp [equal, chk] at source

end Goose.Lower.Validation
