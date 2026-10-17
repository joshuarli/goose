import Goose.Lower.Validation.SourceCanonicalRootFloorsProjection

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound

private theorem keepsSize_pure (value : α) :
    ∀ table, ((pure value : SourceRootsM α) table).2.size = table.size := by intro table; rfl

private theorem keepsSize_bind (action : SourceRootsM α) (next : α → SourceRootsM β)
    (first : ∀ table, (action table).2.size = table.size)
    (rest : ∀ value table, (next value table).2.size = table.size) :
    ∀ table, ((action >>= next) table).2.size = table.size := by
  intro table
  exact (rest (action table).1 (action table).2).trans (first table)

private theorem keepsSize_modify (step : SourceRootTable → SourceRootTable)
    (same : ∀ table, (step table).size = table.size) :
    ∀ table, ((modify step : SourceRootsM Unit) table).2.size = table.size := same

mutual

theorem collectSourceExprRoots_size (env : PEnv) (expression : Expr) :
    ∀ table, (collectSourceExprRoots env expression table).2.size = table.size := by
  cases expression <;> try rw [collectSourceExprRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsSize_pure _
    | exact collectSourceExprRoots_size _ _
    | exact collectSourceExprRoots_size _ _ _
    | exact collectSourcePlaceRoots_size _ _
    | exact collectSourcePlaceRoots_size _ _ _
    | exact collectSourceViewRoots_size _ _
    | exact collectSourceViewRoots_size _ _ _
    | exact collectSourceBoundRoots_size _ _
    | exact collectSourceBoundRoots_size _ _ _
    | exact collectSourceArgumentRoots_size _ _
    | exact collectSourceArgumentRoots_size _ _ _
    | exact collectSourceExprListRoots_size _ _
    | exact collectSourceExprListRoots_size _ _ _
    | exact collectSourceBlockRoots_size _ _
    | exact collectSourceBlockRoots_size _ _ _
    | exact collectSourceStmtListRoots_size _ _
    | exact collectSourceStmtListRoots_size _ _ _
    | exact collectSourcePrintRoots_size _ _
    | exact collectSourcePrintRoots_size _ _ _
    | exact collectSourceStmtRoots_size _ _
    | exact collectSourceStmtRoots_size _ _ _
    | apply keepsSize_bind
    | solve
      | apply keepsSize_modify
        intro table
        split <;> simp
    | (intro value)
    | split
termination_by sizeOf expression

theorem collectSourcePlaceRoots_size (env : PEnv) (place : Place) :
    ∀ table, (collectSourcePlaceRoots env place table).2.size = table.size := by
  cases place <;> try rw [collectSourcePlaceRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsSize_pure _
    | exact collectSourceExprRoots_size _ _
    | exact collectSourceExprRoots_size _ _ _
    | exact collectSourcePlaceRoots_size _ _
    | exact collectSourcePlaceRoots_size _ _ _
    | exact collectSourceViewRoots_size _ _
    | exact collectSourceViewRoots_size _ _ _
    | exact collectSourceBoundRoots_size _ _
    | exact collectSourceBoundRoots_size _ _ _
    | exact collectSourceArgumentRoots_size _ _
    | exact collectSourceArgumentRoots_size _ _ _
    | exact collectSourceExprListRoots_size _ _
    | exact collectSourceExprListRoots_size _ _ _
    | exact collectSourceBlockRoots_size _ _
    | exact collectSourceBlockRoots_size _ _ _
    | exact collectSourceStmtListRoots_size _ _
    | exact collectSourceStmtListRoots_size _ _ _
    | exact collectSourcePrintRoots_size _ _
    | exact collectSourcePrintRoots_size _ _ _
    | exact collectSourceStmtRoots_size _ _
    | exact collectSourceStmtRoots_size _ _ _
    | apply keepsSize_bind
    | solve
      | apply keepsSize_modify
        intro table
        split <;> simp
    | (intro value)
    | split
termination_by sizeOf place

theorem collectSourceViewRoots_size (env : PEnv) (view : View) :
    ∀ table, (collectSourceViewRoots env view table).2.size = table.size := by
  cases view <;> try rw [collectSourceViewRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsSize_pure _
    | exact collectSourceExprRoots_size _ _
    | exact collectSourceExprRoots_size _ _ _
    | exact collectSourcePlaceRoots_size _ _
    | exact collectSourcePlaceRoots_size _ _ _
    | exact collectSourceViewRoots_size _ _
    | exact collectSourceViewRoots_size _ _ _
    | exact collectSourceBoundRoots_size _ _
    | exact collectSourceBoundRoots_size _ _ _
    | exact collectSourceArgumentRoots_size _ _
    | exact collectSourceArgumentRoots_size _ _ _
    | exact collectSourceExprListRoots_size _ _
    | exact collectSourceExprListRoots_size _ _ _
    | exact collectSourceBlockRoots_size _ _
    | exact collectSourceBlockRoots_size _ _ _
    | exact collectSourceStmtListRoots_size _ _
    | exact collectSourceStmtListRoots_size _ _ _
    | exact collectSourcePrintRoots_size _ _
    | exact collectSourcePrintRoots_size _ _ _
    | exact collectSourceStmtRoots_size _ _
    | exact collectSourceStmtRoots_size _ _ _
    | apply keepsSize_bind
    | solve
      | apply keepsSize_modify
        intro table
        split <;> simp
    | (intro value)
    | split
termination_by sizeOf view

theorem collectSourceBoundRoots_size (env : PEnv) (bound : Bound) :
    ∀ table, (collectSourceBoundRoots env bound table).2.size = table.size := by
  cases bound <;> try rw [collectSourceBoundRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsSize_pure _
    | exact collectSourceExprRoots_size _ _
    | exact collectSourceExprRoots_size _ _ _
    | exact collectSourcePlaceRoots_size _ _
    | exact collectSourcePlaceRoots_size _ _ _
    | exact collectSourceViewRoots_size _ _
    | exact collectSourceViewRoots_size _ _ _
    | exact collectSourceBoundRoots_size _ _
    | exact collectSourceBoundRoots_size _ _ _
    | exact collectSourceArgumentRoots_size _ _
    | exact collectSourceArgumentRoots_size _ _ _
    | exact collectSourceExprListRoots_size _ _
    | exact collectSourceExprListRoots_size _ _ _
    | exact collectSourceBlockRoots_size _ _
    | exact collectSourceBlockRoots_size _ _ _
    | exact collectSourceStmtListRoots_size _ _
    | exact collectSourceStmtListRoots_size _ _ _
    | exact collectSourcePrintRoots_size _ _
    | exact collectSourcePrintRoots_size _ _ _
    | exact collectSourceStmtRoots_size _ _
    | exact collectSourceStmtRoots_size _ _ _
    | apply keepsSize_bind
    | solve
      | apply keepsSize_modify
        intro table
        split <;> simp
    | (intro value)
    | split
termination_by sizeOf bound

theorem collectSourceArgumentRoots_size (env : PEnv) (arguments : List Arg) :
    ∀ table, (collectSourceArgumentRoots env arguments table).2.size = table.size := by
  cases arguments
  all_goals try (rename_i argument rest; cases argument)
  all_goals try rw [collectSourceArgumentRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsSize_pure _
    | exact collectSourceExprRoots_size _ _
    | exact collectSourceExprRoots_size _ _ _
    | exact collectSourcePlaceRoots_size _ _
    | exact collectSourcePlaceRoots_size _ _ _
    | exact collectSourceViewRoots_size _ _
    | exact collectSourceViewRoots_size _ _ _
    | exact collectSourceBoundRoots_size _ _
    | exact collectSourceBoundRoots_size _ _ _
    | exact collectSourceArgumentRoots_size _ _
    | exact collectSourceArgumentRoots_size _ _ _
    | exact collectSourceExprListRoots_size _ _
    | exact collectSourceExprListRoots_size _ _ _
    | exact collectSourceBlockRoots_size _ _
    | exact collectSourceBlockRoots_size _ _ _
    | exact collectSourceStmtListRoots_size _ _
    | exact collectSourceStmtListRoots_size _ _ _
    | exact collectSourcePrintRoots_size _ _
    | exact collectSourcePrintRoots_size _ _ _
    | exact collectSourceStmtRoots_size _ _
    | exact collectSourceStmtRoots_size _ _ _
    | apply keepsSize_bind
    | solve
      | apply keepsSize_modify
        intro table
        split <;> simp
    | (intro value)
    | split
termination_by sizeOf arguments

theorem collectSourceExprListRoots_size (env : PEnv) (expressions : List Expr) :
    ∀ table, (collectSourceExprListRoots env expressions table).2.size = table.size := by
  cases expressions <;> try rw [collectSourceExprListRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsSize_pure _
    | exact collectSourceExprRoots_size _ _
    | exact collectSourceExprRoots_size _ _ _
    | exact collectSourcePlaceRoots_size _ _
    | exact collectSourcePlaceRoots_size _ _ _
    | exact collectSourceViewRoots_size _ _
    | exact collectSourceViewRoots_size _ _ _
    | exact collectSourceBoundRoots_size _ _
    | exact collectSourceBoundRoots_size _ _ _
    | exact collectSourceArgumentRoots_size _ _
    | exact collectSourceArgumentRoots_size _ _ _
    | exact collectSourceExprListRoots_size _ _
    | exact collectSourceExprListRoots_size _ _ _
    | exact collectSourceBlockRoots_size _ _
    | exact collectSourceBlockRoots_size _ _ _
    | exact collectSourceStmtListRoots_size _ _
    | exact collectSourceStmtListRoots_size _ _ _
    | exact collectSourcePrintRoots_size _ _
    | exact collectSourcePrintRoots_size _ _ _
    | exact collectSourceStmtRoots_size _ _
    | exact collectSourceStmtRoots_size _ _ _
    | apply keepsSize_bind
    | solve
      | apply keepsSize_modify
        intro table
        split <;> simp
    | (intro value)
    | split
termination_by sizeOf expressions

theorem collectSourceBlockRoots_size (env : PEnv) (body : Block) :
    ∀ table, (collectSourceBlockRoots env body table).2.size = table.size := by
  cases body <;> try rw [collectSourceBlockRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsSize_pure _
    | exact collectSourceExprRoots_size _ _
    | exact collectSourceExprRoots_size _ _ _
    | exact collectSourcePlaceRoots_size _ _
    | exact collectSourcePlaceRoots_size _ _ _
    | exact collectSourceViewRoots_size _ _
    | exact collectSourceViewRoots_size _ _ _
    | exact collectSourceBoundRoots_size _ _
    | exact collectSourceBoundRoots_size _ _ _
    | exact collectSourceArgumentRoots_size _ _
    | exact collectSourceArgumentRoots_size _ _ _
    | exact collectSourceExprListRoots_size _ _
    | exact collectSourceExprListRoots_size _ _ _
    | exact collectSourceBlockRoots_size _ _
    | exact collectSourceBlockRoots_size _ _ _
    | exact collectSourceStmtListRoots_size _ _
    | exact collectSourceStmtListRoots_size _ _ _
    | exact collectSourcePrintRoots_size _ _
    | exact collectSourcePrintRoots_size _ _ _
    | exact collectSourceStmtRoots_size _ _
    | exact collectSourceStmtRoots_size _ _ _
    | apply keepsSize_bind
    | solve
      | apply keepsSize_modify
        intro table
        split <;> simp
    | (intro value)
    | split
termination_by sizeOf body

theorem collectSourceStmtListRoots_size (env : PEnv) (statements : List Stmt) :
    ∀ table, (collectSourceStmtListRoots env statements table).2.size = table.size := by
  cases statements <;> try rw [collectSourceStmtListRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsSize_pure _
    | exact collectSourceExprRoots_size _ _
    | exact collectSourceExprRoots_size _ _ _
    | exact collectSourcePlaceRoots_size _ _
    | exact collectSourcePlaceRoots_size _ _ _
    | exact collectSourceViewRoots_size _ _
    | exact collectSourceViewRoots_size _ _ _
    | exact collectSourceBoundRoots_size _ _
    | exact collectSourceBoundRoots_size _ _ _
    | exact collectSourceArgumentRoots_size _ _
    | exact collectSourceArgumentRoots_size _ _ _
    | exact collectSourceExprListRoots_size _ _
    | exact collectSourceExprListRoots_size _ _ _
    | exact collectSourceBlockRoots_size _ _
    | exact collectSourceBlockRoots_size _ _ _
    | exact collectSourceStmtListRoots_size _ _
    | exact collectSourceStmtListRoots_size _ _ _
    | exact collectSourcePrintRoots_size _ _
    | exact collectSourcePrintRoots_size _ _ _
    | exact collectSourceStmtRoots_size _ _
    | exact collectSourceStmtRoots_size _ _ _
    | apply keepsSize_bind
    | solve
      | apply keepsSize_modify
        intro table
        split <;> simp
    | (intro value)
    | split
termination_by sizeOf statements

theorem collectSourcePrintRoots_size (env : PEnv) (arguments : List PrintArg) :
    ∀ table, (collectSourcePrintRoots env arguments table).2.size = table.size := by
  cases arguments
  all_goals try (rename_i argument rest; cases argument)
  all_goals try rw [collectSourcePrintRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsSize_pure _
    | exact collectSourceExprRoots_size _ _
    | exact collectSourceExprRoots_size _ _ _
    | exact collectSourcePlaceRoots_size _ _
    | exact collectSourcePlaceRoots_size _ _ _
    | exact collectSourceViewRoots_size _ _
    | exact collectSourceViewRoots_size _ _ _
    | exact collectSourceBoundRoots_size _ _
    | exact collectSourceBoundRoots_size _ _ _
    | exact collectSourceArgumentRoots_size _ _
    | exact collectSourceArgumentRoots_size _ _ _
    | exact collectSourceExprListRoots_size _ _
    | exact collectSourceExprListRoots_size _ _ _
    | exact collectSourceBlockRoots_size _ _
    | exact collectSourceBlockRoots_size _ _ _
    | exact collectSourceStmtListRoots_size _ _
    | exact collectSourceStmtListRoots_size _ _ _
    | exact collectSourcePrintRoots_size _ _
    | exact collectSourcePrintRoots_size _ _ _
    | exact collectSourceStmtRoots_size _ _
    | exact collectSourceStmtRoots_size _ _ _
    | apply keepsSize_bind
    | solve
      | apply keepsSize_modify
        intro table
        split <;> simp
    | (intro value)
    | split
termination_by sizeOf arguments

theorem collectSourceStmtRoots_size (env : PEnv) (statement : Stmt) :
    ∀ table, (collectSourceStmtRoots env statement table).2.size = table.size := by
  cases statement
  case ret value origin =>
    cases value with
    | none => intro table; rw [collectSourceStmtRoots.eq_def]; rfl
    | some expression =>
        rw [collectSourceStmtRoots.eq_def]
        exact keepsSize_bind _ _ (collectSourceExprRoots_size env expression)
          (fun _ => keepsSize_pure ())
  all_goals try rw [collectSourceStmtRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact keepsSize_pure _
    | exact collectSourceExprRoots_size _ _
    | exact collectSourceExprRoots_size _ _ _
    | exact collectSourcePlaceRoots_size _ _
    | exact collectSourcePlaceRoots_size _ _ _
    | exact collectSourceViewRoots_size _ _
    | exact collectSourceViewRoots_size _ _ _
    | exact collectSourceBoundRoots_size _ _
    | exact collectSourceBoundRoots_size _ _ _
    | exact collectSourceArgumentRoots_size _ _
    | exact collectSourceArgumentRoots_size _ _ _
    | exact collectSourceExprListRoots_size _ _
    | exact collectSourceExprListRoots_size _ _ _
    | exact collectSourceBlockRoots_size _ _
    | exact collectSourceBlockRoots_size _ _ _
    | exact collectSourceStmtListRoots_size _ _
    | exact collectSourceStmtListRoots_size _ _ _
    | exact collectSourcePrintRoots_size _ _
    | exact collectSourcePrintRoots_size _ _ _
    | exact collectSourceStmtRoots_size _ _
    | exact collectSourceStmtRoots_size _ _ _
    | apply keepsSize_bind
    | solve
      | apply keepsSize_modify
        intro table
        split <;> simp
    | (intro value)
    | split
termination_by sizeOf statement

end

theorem collectSourceExprRoots_ifE_checkpoint (env : PEnv)
    (condition : Expr) (yes no : Block) (table : SourceRootTable)
    (bounded : sourceBlockScope yes < table.size)
    {before after : RState} {roots : List RootRef}
    (checked : rpExpr env (.ifE condition yes no) before = .ok (roots, after)) :
    ((collectSourceExprRoots env (.ifE condition yes no) table).2)[sourceBlockScope yes]? =
      some (some roots) := by
  let afterCondition := (collectSourceExprRoots env condition table).2
  let afterYes := (collectSourceBlockRoots env yes afterCondition).2
  let afterNo := (collectSourceBlockRoots env no afterYes).2
  have sizeCondition : afterCondition.size = table.size := collectSourceExprRoots_size env condition table
  have sizeYes : afterYes.size = table.size :=
    (collectSourceBlockRoots_size env yes afterCondition).trans sizeCondition
  have sizeNo : afterNo.size = table.size :=
    (collectSourceBlockRoots_size env no afterYes).trans sizeYes
  have inside : sourceBlockScope yes < afterNo.size := sizeNo ▸ bounded
  have projected := collectSourceExprRoots_agrees env (.ifE condition yes no) table checked
  change unionRoots (collectSourceBlockRoots env yes afterCondition).1
    (collectSourceBlockRoots env no afterYes).1 = roots at projected
  change ((if sourceBlockScope yes < afterNo.size then
    afterNo.set! (sourceBlockScope yes) (some (unionRoots
      (collectSourceBlockRoots env yes afterCondition).1
      (collectSourceBlockRoots env no afterYes).1)) else afterNo)[sourceBlockScope yes]?) = _
  simp [inside, projected]

end Goose.Lower.Validation.SourceCanonicalRootFloors
