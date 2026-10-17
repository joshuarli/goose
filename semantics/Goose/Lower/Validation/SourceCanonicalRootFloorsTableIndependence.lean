import Lean.Meta.Tactic.Cases
import Goose.Lower.Validation.SourceCanonicalRootFloorsProjection

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core

def SourceResultIndependent (action : SourceRootsM α) : Prop :=
  ∀ first second, (action first).1 = (action second).1

local syntax "independent_action " ident : tactic
elab_rules : tactic
  | `(tactic| independent_action $expected:ident) => Lean.Elab.Tactic.withMainContext do
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      unless target.getAppFn.isConstOf ``SourceResultIndependent do
        Lean.throwError "expected independent source result"
      let mut action := target.getAppArgs.back!
      repeat
        action := action.headBeta
        if let .letE _ _ value body _ := action then
          action := body.instantiate1 value
        else if let .reduced reduced ← Lean.Meta.reduceMatcher? action then
          action := reduced
        else
          break
      let .const actual _ := action.getAppFn
        | Lean.throwError "expected source collector action"
      unless actual.getString! == expected.getId.getString! do
        Lean.throwError "different source collector action"

local syntax "independent_callback" : tactic
elab_rules : tactic
  | `(tactic| independent_callback) => do
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let .forallE _ _ body _ := target
        | Lean.throwError "expected independent continuation"
      unless body.getAppFn.isConstOf ``SourceResultIndependent do
        Lean.throwError "expected independent continuation"
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro value))

private theorem independent_pure (value : α) : SourceResultIndependent (pure value) := by
  intro first second
  rfl

private theorem independent_unit (action : SourceRootsM Unit) : SourceResultIndependent action := by
  intro first second
  exact Subsingleton.elim _ _

private theorem independent_bind (action : SourceRootsM α) (next : α → SourceRootsM β)
    (first : SourceResultIndependent action) (rest : ∀ value, SourceResultIndependent (next value)) :
    SourceResultIndependent (action >>= next) := by
  intro left right
  change (next (action left).1 (action left).2).1 = (next (action right).1 (action right).2).1
  rw [first left right]
  exact rest (action right).1 (action left).2 (action right).2

private theorem independent_discard (action : SourceRootsM α) (next : SourceRootsM β)
    (rest : SourceResultIndependent next) :
    SourceResultIndependent (do let _ ← action; next) := by
  intro left right
  exact rest (action left).2 (action right).2

mutual

theorem collectSourceExprRoots_independent (env : PEnv) (expression : Expr) :
    SourceResultIndependent (collectSourceExprRoots env expression) := by
  cases expression
  all_goals try rw [collectSourceExprRoots.eq_def]
  all_goals repeat' first
    | exact independent_unit _
    | (independent_action pure; apply independent_pure)
    | (solve | independent_action collectSourceExprRoots; exact collectSourceExprRoots_independent _ _)
    | (solve | independent_action collectSourcePlaceRoots; exact collectSourcePlaceRoots_independent _ _)
    | (solve | independent_action collectSourceViewRoots; exact collectSourceViewRoots_independent _ _)
    | (solve | independent_action collectSourceArgumentRoots; exact collectSourceArgumentRoots_independent _ _)
    | (solve | independent_action collectSourceBlockRoots; exact collectSourceBlockRoots_independent _ _)
    | (independent_action bind; apply independent_discard)
    | (independent_action bind; apply independent_bind)
    | independent_callback
termination_by sizeOf expression

theorem collectSourcePlaceRoots_independent (env : PEnv) (place : Place) :
    SourceResultIndependent (collectSourcePlaceRoots env place) := by
  cases place
  all_goals try rw [collectSourcePlaceRoots.eq_def]
  all_goals repeat' first
    | exact independent_unit _
    | (independent_action pure; apply independent_pure)
    | (solve | independent_action collectSourceExprRoots; exact collectSourceExprRoots_independent _ _)
    | (solve | independent_action collectSourcePlaceRoots; exact collectSourcePlaceRoots_independent _ _)
    | (solve | independent_action collectSourceViewRoots; exact collectSourceViewRoots_independent _ _)
    | (solve | independent_action collectSourceArgumentRoots; exact collectSourceArgumentRoots_independent _ _)
    | (solve | independent_action collectSourceBlockRoots; exact collectSourceBlockRoots_independent _ _)
    | (independent_action bind; apply independent_discard)
    | (independent_action bind; apply independent_bind)
    | independent_callback
termination_by sizeOf place

theorem collectSourceViewRoots_independent (env : PEnv) (view : View) :
    SourceResultIndependent (collectSourceViewRoots env view) := by
  cases view
  all_goals try rw [collectSourceViewRoots.eq_def]
  all_goals repeat' first
    | exact independent_unit _
    | (independent_action pure; apply independent_pure)
    | (solve | independent_action collectSourceExprRoots; exact collectSourceExprRoots_independent _ _)
    | (solve | independent_action collectSourcePlaceRoots; exact collectSourcePlaceRoots_independent _ _)
    | (solve | independent_action collectSourceViewRoots; exact collectSourceViewRoots_independent _ _)
    | (solve | independent_action collectSourceArgumentRoots; exact collectSourceArgumentRoots_independent _ _)
    | (solve | independent_action collectSourceBlockRoots; exact collectSourceBlockRoots_independent _ _)
    | (independent_action bind; apply independent_discard)
    | (independent_action bind; apply independent_bind)
    | independent_callback
termination_by sizeOf view

theorem collectSourceArgumentRoots_independent (env : PEnv) (arguments : List Arg) :
    SourceResultIndependent (collectSourceArgumentRoots env arguments) := by
  cases arguments
  all_goals try (rename_i head rest; cases head)
  all_goals try rw [collectSourceArgumentRoots.eq_def]
  all_goals repeat' first
    | exact independent_unit _
    | (independent_action pure; apply independent_pure)
    | (solve | independent_action collectSourceExprRoots; exact collectSourceExprRoots_independent _ _)
    | (solve | independent_action collectSourcePlaceRoots; exact collectSourcePlaceRoots_independent _ _)
    | (solve | independent_action collectSourceViewRoots; exact collectSourceViewRoots_independent _ _)
    | (solve | independent_action collectSourceArgumentRoots; exact collectSourceArgumentRoots_independent _ _)
    | (solve | independent_action collectSourceBlockRoots; exact collectSourceBlockRoots_independent _ _)
    | (independent_action bind; apply independent_discard)
    | (independent_action bind; apply independent_bind)
    | independent_callback
termination_by sizeOf arguments

theorem collectSourceBlockRoots_independent (env : PEnv) (body : Block) :
    SourceResultIndependent (collectSourceBlockRoots env body) := by
  cases body
  all_goals try (rename_i scope statements value; cases value)
  all_goals try rw [collectSourceBlockRoots.eq_def]
  all_goals repeat' first
    | exact independent_unit _
    | (independent_action pure; apply independent_pure)
    | (solve | independent_action collectSourceExprRoots; exact collectSourceExprRoots_independent _ _)
    | (solve | independent_action collectSourcePlaceRoots; exact collectSourcePlaceRoots_independent _ _)
    | (solve | independent_action collectSourceViewRoots; exact collectSourceViewRoots_independent _ _)
    | (solve | independent_action collectSourceArgumentRoots; exact collectSourceArgumentRoots_independent _ _)
    | (solve | independent_action collectSourceBlockRoots; exact collectSourceBlockRoots_independent _ _)
    | (independent_action bind; apply independent_discard)
    | (independent_action bind; apply independent_bind)
    | independent_callback
termination_by sizeOf body

end

end Goose.Lower.Validation.SourceCanonicalRootFloors
