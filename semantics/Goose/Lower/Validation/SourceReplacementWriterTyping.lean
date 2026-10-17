import Goose.Lower.Validation.SourceReplacementLexicalWritersAccepted
import Goose.Lower.Validation.StorageWalkSourceParameters
import Goose.Lower.Validation.SourceStatementTyping
import Goose.Lower.Validation.ExpressionTypingScalarOps
import Goose.Lower.Validation.ExpressionTypingSliceOps
import Goose.Lower.Validation.SummaryPreservationReplayIfSource
import Goose.Lower.Validation.SummaryPreservationReplayArgumentSource

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound SourceReplacementLexicalWriters

inductive NodeTyped (env : TEnv) : DemandNode → Prop
  | expression {expression type start finish}
      (typed : Core.tyExpr env expression start = .ok (type, finish)) : NodeTyped env (.expression expression)
  | sliceReference {expression type}
      (typed : Core.sliceRefTy env expression = some type) : NodeTyped env (.expression expression)
  | place {place info start finish}
      (typed : Core.tyPlace env place start = .ok (info, finish)) : NodeTyped env (.place place)
  | view {view info start finish}
      (typed : Core.tyView env view start = .ok (info, finish)) : NodeTyped env (.view view)
  | bound {bound start finish}
      (typed : Core.tyBound env bound start = .ok ((), finish)) : NodeTyped env (.bound bound)
  | statement {statement scope output start finish}
      (active : scope ∈ env.scopes)
      (typed : Core.tyStmt env scope statement start = .ok (output, finish)) : NodeTyped env (.statement statement)
  | block {block type start finish}
      (typed : Core.tyBlock env [] block start = .ok (type, finish)) : NodeTyped env (.block block)

theorem tyStmt_scopes {env after : TEnv} {scope start finish : Nat} (stmt : Stmt)
    (typed : tyStmt env scope stmt start = .ok (after, finish)) : after.scopes = env.scopes := by
  cases stmt
  case' resize owner size fill origin => cases fill
  case' ifS condition thenBlock otherwise origin => cases otherwise
  case' ret value origin => cases value
  all_goals simp only [tyStmt] at typed
  all_goals
    repeat' first
    | (subst after; rfl)
    | contradiction
    | (simp only [chk, false_and, and_false, exists_false, exists_const, or_false, false_or,
        true_and, Prod.mk.injEq, Prod.exists, and_assoc, exists_eq_left, exists_and_left] at typed)
    | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
    | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
    | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
    | (split at typed)

theorem tyStmts_scopes {env after : TEnv} {scope start finish : Nat} {statements : List Stmt}
    (typed : tyStmts env scope statements start = .ok (after, finish)) : after.scopes = env.scopes := by
  induction statements generalizing env start with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).mp typed
    rfl
  | cons statement statements ih =>
    obtain ⟨middle, next, head, tail⟩ := tyStmts_cons_children typed
    exact (ih tail).trans (tyStmt_scopes statement head)

theorem declarePre_scopes {env after : TEnv} {scope start finish : Nat} {pre : List (VarId × Ty)}
    (typed : declarePre env scope pre start = .ok (after, finish)) : after.scopes = env.scopes := by
  induction pre generalizing env start with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).mp typed
    rfl
  | cons binding rest ih =>
    obtain ⟨index, type⟩ := binding
    obtain ⟨localVar, next, declared, shape, tail⟩ := declarePre_cons_children typed
    exact ih (env := { env with visible := index :: env.visible }) tail

structure ChildContext (env : TEnv) (parent child : DemandNode) (after : TEnv) : Prop where
  moduleEq : after.mod = env.mod
  varsEq : after.vars = env.vars
  implEq : after.impl = env.impl
  scopesEq : after.scopes = (ownScopeKeys parent).reverse ++ env.scopes
  visible : ∀ stack, StorageWalkVisible env (ownScopeKeys parent ++ stack) →
    StorageWalkVisible after (ownScopeKeys child ++ stack ++ ownScopeKeys parent)

theorem ChildContext.same (env : TEnv) {parent child : DemandNode} (empty : ownScopeKeys parent = []) :
    ChildContext env parent child env := by
  refine ⟨rfl, rfl, rfl, by simp [empty], ?_⟩
  intro stack visible
  simp only [empty, List.nil_append] at visible
  simp only [empty, List.append_nil]
  exact visible.mono (fun scope member => List.mem_append_right _ member)

theorem ChildContext.expressionEnv (env : TEnv) {parent child : DemandNode}
    (empty : ownScopeKeys parent = []) : ChildContext env parent child (exprEnv env) := by
  have same := ChildContext.same env (child := child) empty
  exact ⟨same.moduleEq, same.varsEq, same.implEq, same.scopesEq, same.visible⟩

theorem NodeTyped.call {env : TEnv} {function : ContextId} {arguments : List Arg} {origin : OriginId}
    (typed : NodeTyped env (.expression (.call function arguments origin))) :
    ∃ type start finish, Core.tyExpr env (.call function arguments origin) start = .ok (type, finish) := by
  cases typed with
  | expression source => exact ⟨_, _, _, source⟩
  | sliceReference source => simp [Core.sliceRefTy] at source

theorem NodeTyped.statement_typing {env : TEnv} {statement : Stmt}
    (typed : NodeTyped env (.statement statement)) :
    ∃ scope output start finish, scope ∈ env.scopes ∧ Core.tyStmt env scope statement start = .ok (output, finish) := by
  cases typed with
  | statement active source => exact ⟨_, _, _, _, active, source⟩

end Goose.Lower.Validation.SourceReplacementWriterTyping
