import Goose.Lower.Validation.SummaryPreservationRefinedEffects
import Goose.Core.Sound.Invert

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem tyExpr_shortCircuit_children (isAnd : Bool) {env : TEnv} {left right : Expr}
    {start finish : Nat} {type : Ty}
    (source : tyExpr env (if isAnd then .and left right else .or left right) start = .ok (type, finish)) :
    type = .bool ∧ ∃ middle, tyExpr env left start = .ok (.bool, middle) ∧
      tyExpr env right middle = .ok (.bool, finish) := by
  cases isAnd <;> simp only [Bool.false_eq_true, ite_false, ite_true, tyExpr] at source
  all_goals inv at source
  all_goals
    obtain ⟨leftType, middle, leftTyped, leftBool, rightType, finalCounter, rightTyped, rightBool,
      typeEq, finishEq⟩ := source
    subst leftType
    subst rightType
    subst type
    subst finish
    exact ⟨rfl, middle, leftTyped, rightTyped⟩

theorem rpExpr_shortCircuit_children (isAnd : Bool) {env : PEnv} {left right : Expr}
    {before after : RState} {sourceRoots : List RootRef}
    (source : rpExpr env (if isAnd then .and left right else .or left right) before = .ok (sourceRoots, after)) :
    sourceRoots = [] ∧ ∃ leftRoots middle rightRoots,
      rpExpr env left before = .ok (leftRoots, middle) ∧
      rpExpr env right middle = .ok (rightRoots, after) := by
  cases isAnd <;> simp only [Bool.false_eq_true, ite_false, ite_true, rpExpr] at source
  all_goals
    obtain ⟨leftRoots, middle, firstReplay, tail⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨rightRoots, finalState, rightReplay, result⟩ := (st_bind_ok _ _ _ _).mp tail
    have equal := (st_pure_ok _ _ _).mp result
    cases equal
    exact ⟨rfl, leftRoots, middle, rightRoots, firstReplay, rightReplay⟩

end Goose.Lower.Validation.SummaryPreservation
