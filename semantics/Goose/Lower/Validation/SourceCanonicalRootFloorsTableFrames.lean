import Lean.Meta.Tactic.Cases
import Goose.Lower.Validation.SourceCanonicalRootFloorsScopeKeys

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

local syntax "source_split_ands" : tactic
elab_rules : tactic
  | `(tactic| source_split_ands) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      return [← goal.casesAnd]

open Goose.Core

private theorem keepsIndex_pure (value : α) (index : Nat) :
    ∀ table, ((pure value : SourceRootsM α) table).2[index]? = table[index]? := by
  intro table
  rfl

private theorem keepsIndex_bind (action : SourceRootsM α) (next : α → SourceRootsM β)
    (index : Nat) (first : ∀ table, (action table).2[index]? = table[index]?)
    (rest : ∀ value table, (next value table).2[index]? = table[index]?) :
    ∀ table, ((action >>= next) table).2[index]? = table[index]? := by
  intro table
  exact (rest (action table).1 (action table).2).trans (first table)

private theorem keepsIndex_write (index scope : Nat) (roots : List RootRef)
    (different : index ≠ scope) :
    ∀ table, ((modify fun table => if scope < table.size then table.set! scope (some roots)
      else table : SourceRootsM Unit) table).2[index]? = table[index]? := by
  intro table
  change (if scope < table.size then table.set! scope (some roots) else table)[index]? = _
  split <;> simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, different, Ne.symm different]

private theorem block_scope_different (body : Block) (index : Nat)
    (outside : index ∉ (blockScopes none body).map Prod.fst) :
    index ≠ sourceBlockScope body := by
  cases body with
  | mk scope statements value =>
      intro same
      apply outside
      cases value <;> simp [blockScopes, sourceBlockScope, same]

mutual

theorem collectSourceExprRoots_outside (env : PEnv) (expression : Expr) (index : Nat)
    (outside : index ∉ (exprScopes none expression).map Prod.fst) :
    ∀ table, (collectSourceExprRoots env expression table).2[index]? = table[index]? := by
  cases expression
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
  all_goals source_split_ands
  all_goals try rw [collectSourceExprRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsIndex_pure _ _
    | (apply collectSourceExprRoots_outside _ _ index; assumption)
    | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
    | (apply collectSourceViewRoots_outside _ _ index; assumption)
    | (apply collectSourceBoundRoots_outside _ _ index; assumption)
    | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
    | (apply collectSourceExprListRoots_outside _ _ index; assumption)
    | (apply collectSourceBlockRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
    | (apply collectSourcePrintRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtRoots_outside _ _ index; assumption)
    | apply keepsIndex_bind
    | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
    | (intro value)
    | split
termination_by sizeOf expression

theorem collectSourcePlaceRoots_outside (env : PEnv) (place : Place) (index : Nat)
    (outside : index ∉ (placeScopes none place).map Prod.fst) :
    ∀ table, (collectSourcePlaceRoots env place table).2[index]? = table[index]? := by
  cases place
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
  all_goals source_split_ands
  all_goals try rw [collectSourcePlaceRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsIndex_pure _ _
    | (apply collectSourceExprRoots_outside _ _ index; assumption)
    | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
    | (apply collectSourceViewRoots_outside _ _ index; assumption)
    | (apply collectSourceBoundRoots_outside _ _ index; assumption)
    | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
    | (apply collectSourceExprListRoots_outside _ _ index; assumption)
    | (apply collectSourceBlockRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
    | (apply collectSourcePrintRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtRoots_outside _ _ index; assumption)
    | apply keepsIndex_bind
    | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
    | (intro value)
    | split
termination_by sizeOf place

theorem collectSourceViewRoots_outside (env : PEnv) (view : View) (index : Nat)
    (outside : index ∉ (viewScopes none view).map Prod.fst) :
    ∀ table, (collectSourceViewRoots env view table).2[index]? = table[index]? := by
  cases view
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
  all_goals source_split_ands
  all_goals try rw [collectSourceViewRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsIndex_pure _ _
    | (apply collectSourceExprRoots_outside _ _ index; assumption)
    | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
    | (apply collectSourceViewRoots_outside _ _ index; assumption)
    | (apply collectSourceBoundRoots_outside _ _ index; assumption)
    | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
    | (apply collectSourceExprListRoots_outside _ _ index; assumption)
    | (apply collectSourceBlockRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
    | (apply collectSourcePrintRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtRoots_outside _ _ index; assumption)
    | apply keepsIndex_bind
    | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
    | (intro value)
    | split
termination_by sizeOf view

theorem collectSourceBoundRoots_outside (env : PEnv) (bound : Bound) (index : Nat)
    (outside : index ∉ (boundScopes none bound).map Prod.fst) :
    ∀ table, (collectSourceBoundRoots env bound table).2[index]? = table[index]? := by
  cases bound
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
  all_goals source_split_ands
  all_goals try rw [collectSourceBoundRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsIndex_pure _ _
    | (apply collectSourceExprRoots_outside _ _ index; assumption)
    | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
    | (apply collectSourceViewRoots_outside _ _ index; assumption)
    | (apply collectSourceBoundRoots_outside _ _ index; assumption)
    | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
    | (apply collectSourceExprListRoots_outside _ _ index; assumption)
    | (apply collectSourceBlockRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
    | (apply collectSourcePrintRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtRoots_outside _ _ index; assumption)
    | apply keepsIndex_bind
    | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
    | (intro value)
    | split
termination_by sizeOf bound

theorem collectSourceArgumentRoots_outside (env : PEnv) (arguments : List Arg) (index : Nat)
    (outside : index ∉ (argsScopes none arguments).map Prod.fst) :
    ∀ table, (collectSourceArgumentRoots env arguments table).2[index]? = table[index]? := by
  cases arguments
  all_goals try (rename_i head rest; cases head)
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
  all_goals source_split_ands
  all_goals try rw [collectSourceArgumentRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsIndex_pure _ _
    | (apply collectSourceExprRoots_outside _ _ index; assumption)
    | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
    | (apply collectSourceViewRoots_outside _ _ index; assumption)
    | (apply collectSourceBoundRoots_outside _ _ index; assumption)
    | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
    | (apply collectSourceExprListRoots_outside _ _ index; assumption)
    | (apply collectSourceBlockRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
    | (apply collectSourcePrintRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtRoots_outside _ _ index; assumption)
    | apply keepsIndex_bind
    | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
    | (intro value)
    | split
termination_by sizeOf arguments

theorem collectSourceExprListRoots_outside (env : PEnv) (expressions : List Expr) (index : Nat)
    (outside : index ∉ (exprsScopes none expressions).map Prod.fst) :
    ∀ table, (collectSourceExprListRoots env expressions table).2[index]? = table[index]? := by
  cases expressions
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
  all_goals source_split_ands
  all_goals try rw [collectSourceExprListRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsIndex_pure _ _
    | (apply collectSourceExprRoots_outside _ _ index; assumption)
    | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
    | (apply collectSourceViewRoots_outside _ _ index; assumption)
    | (apply collectSourceBoundRoots_outside _ _ index; assumption)
    | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
    | (apply collectSourceExprListRoots_outside _ _ index; assumption)
    | (apply collectSourceBlockRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
    | (apply collectSourcePrintRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtRoots_outside _ _ index; assumption)
    | apply keepsIndex_bind
    | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
    | (intro value)
    | split
termination_by sizeOf expressions

theorem collectSourceBlockRoots_outside (env : PEnv) (body : Block) (index : Nat)
    (outside : index ∉ (blockScopes none body).map Prod.fst) :
    ∀ table, (collectSourceBlockRoots env body table).2[index]? = table[index]? := by
  cases body
  all_goals try (rename_i scope statements value; cases value)
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
  all_goals source_split_ands
  all_goals try rw [collectSourceBlockRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsIndex_pure _ _
    | (apply collectSourceExprRoots_outside _ _ index; assumption)
    | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
    | (apply collectSourceViewRoots_outside _ _ index; assumption)
    | (apply collectSourceBoundRoots_outside _ _ index; assumption)
    | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
    | (apply collectSourceExprListRoots_outside _ _ index; assumption)
    | (apply collectSourceBlockRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
    | (apply collectSourcePrintRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtRoots_outside _ _ index; assumption)
    | apply keepsIndex_bind
    | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
    | (intro value)
    | split
termination_by sizeOf body

theorem collectSourceStmtListRoots_outside (env : PEnv) (statements : List Stmt) (index : Nat)
    (outside : index ∉ (stmtsScopes none statements).map Prod.fst) :
    ∀ table, (collectSourceStmtListRoots env statements table).2[index]? = table[index]? := by
  cases statements
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
  all_goals source_split_ands
  all_goals try rw [collectSourceStmtListRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsIndex_pure _ _
    | (apply collectSourceExprRoots_outside _ _ index; assumption)
    | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
    | (apply collectSourceViewRoots_outside _ _ index; assumption)
    | (apply collectSourceBoundRoots_outside _ _ index; assumption)
    | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
    | (apply collectSourceExprListRoots_outside _ _ index; assumption)
    | (apply collectSourceBlockRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
    | (apply collectSourcePrintRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtRoots_outside _ _ index; assumption)
    | apply keepsIndex_bind
    | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
    | (intro value)
    | split
termination_by sizeOf statements

theorem collectSourcePrintRoots_outside (env : PEnv) (arguments : List PrintArg) (index : Nat)
    (outside : index ∉ (printScopes none arguments).map Prod.fst) :
    ∀ table, (collectSourcePrintRoots env arguments table).2[index]? = table[index]? := by
  cases arguments
  all_goals try (rename_i head rest; cases head)
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
  all_goals source_split_ands
  all_goals try rw [collectSourcePrintRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsIndex_pure _ _
    | (apply collectSourceExprRoots_outside _ _ index; assumption)
    | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
    | (apply collectSourceViewRoots_outside _ _ index; assumption)
    | (apply collectSourceBoundRoots_outside _ _ index; assumption)
    | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
    | (apply collectSourceExprListRoots_outside _ _ index; assumption)
    | (apply collectSourceBlockRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
    | (apply collectSourcePrintRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtRoots_outside _ _ index; assumption)
    | apply keepsIndex_bind
    | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
    | (intro value)
    | split
termination_by sizeOf arguments

theorem collectSourceStmtRoots_outside (env : PEnv) (statement : Stmt) (index : Nat)
    (outside : index ∉ (stmtScopes none statement).map Prod.fst) :
    ∀ table, (collectSourceStmtRoots env statement table).2[index]? = table[index]? := by
  cases statement
  case ret value origin =>
    cases value
    all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
    all_goals source_split_ands
    all_goals try rw [collectSourceStmtRoots.eq_def]
    all_goals repeat' first
      | rfl
      | exact keepsIndex_pure _ _
      | (apply collectSourceExprRoots_outside _ _ index; assumption)
      | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
      | (apply collectSourceViewRoots_outside _ _ index; assumption)
      | (apply collectSourceBoundRoots_outside _ _ index; assumption)
      | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
      | (apply collectSourceExprListRoots_outside _ _ index; assumption)
      | (apply collectSourceBlockRoots_outside _ _ index; assumption)
      | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
      | (apply collectSourcePrintRoots_outside _ _ index; assumption)
      | (apply collectSourceStmtRoots_outside _ _ index; assumption)
      | apply keepsIndex_bind
      | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
      | (intro value)
      | split
  case resize owner count fill origin =>
    cases fill
    all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
    all_goals source_split_ands
    all_goals try rw [collectSourceStmtRoots.eq_def]
    all_goals repeat' first
      | rfl
      | exact keepsIndex_pure _ _
      | (apply collectSourceExprRoots_outside _ _ index; assumption)
      | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
      | (apply collectSourceViewRoots_outside _ _ index; assumption)
      | (apply collectSourceBoundRoots_outside _ _ index; assumption)
      | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
      | (apply collectSourceExprListRoots_outside _ _ index; assumption)
      | (apply collectSourceBlockRoots_outside _ _ index; assumption)
      | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
      | (apply collectSourcePrintRoots_outside _ _ index; assumption)
      | (apply collectSourceStmtRoots_outside _ _ index; assumption)
      | apply keepsIndex_bind
      | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
      | (intro value)
      | split
  case ifS condition yes no origin =>
    cases no
    all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
    all_goals source_split_ands
    all_goals try rw [collectSourceStmtRoots.eq_def]
    all_goals repeat' first
      | rfl
      | exact keepsIndex_pure _ _
      | (apply collectSourceExprRoots_outside _ _ index; assumption)
      | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
      | (apply collectSourceViewRoots_outside _ _ index; assumption)
      | (apply collectSourceBoundRoots_outside _ _ index; assumption)
      | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
      | (apply collectSourceExprListRoots_outside _ _ index; assumption)
      | (apply collectSourceBlockRoots_outside _ _ index; assumption)
      | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
      | (apply collectSourcePrintRoots_outside _ _ index; assumption)
      | (apply collectSourceStmtRoots_outside _ _ index; assumption)
      | apply keepsIndex_bind
      | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
      | (intro value)
      | split
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, not_or, exprScopes_keys_none, placeScopes_keys_none, viewScopes_keys_none, boundScopes_keys_none, argsScopes_keys_none, exprsScopes_keys_none, blockScopes_keys_none, stmtsScopes_keys_none, printScopes_keys_none, stmtScopes_keys_none] at outside
  all_goals source_split_ands
  all_goals try rw [collectSourceStmtRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsIndex_pure _ _
    | (apply collectSourceExprRoots_outside _ _ index; assumption)
    | (apply collectSourcePlaceRoots_outside _ _ index; assumption)
    | (apply collectSourceViewRoots_outside _ _ index; assumption)
    | (apply collectSourceBoundRoots_outside _ _ index; assumption)
    | (apply collectSourceArgumentRoots_outside _ _ index; assumption)
    | (apply collectSourceExprListRoots_outside _ _ index; assumption)
    | (apply collectSourceBlockRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtListRoots_outside _ _ index; assumption)
    | (apply collectSourcePrintRoots_outside _ _ index; assumption)
    | (apply collectSourceStmtRoots_outside _ _ index; assumption)
    | apply keepsIndex_bind
    | (apply keepsIndex_write; first | assumption | (apply block_scope_different; assumption))
    | (intro value)
    | split
termination_by sizeOf statement

end

end Goose.Lower.Validation.SourceCanonicalRootFloors
