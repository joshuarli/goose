import Goose.Lower.Validation.ReplacementScopedOperandsBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem rhsOperands_slice (floor : Nat) (mu : Mutability) (view : View)
    (lo hi : Bound) (origin : OriginId)
    (viewChild : RhsOperandsRun floor (lowerView view))
    (loChild : RhsOperandsRun floor (lowerBound lo)) (hiChild : RhsOperandsRun floor (lowerBound hi)) :
    RhsOperandsRun floor (lowerExpr (.slice mu view lo hi origin)) := by
  intro env before bound
  simp only [lowerExpr]
  apply RhsOperandsAt.bindFresh bound (viewChild env before bound)
    (advB_lowerView view) (freshValue_lowerView view)
  intro value viewed _ viewedBound valueFresh
  apply RhsOperandsAt.bindRun (loChild env viewed viewedBound)
  intro low lowered lowRun
  have lowerBound := Nat.le_trans viewedBound (advB_lowerBound lo env viewed low lowered lowRun).vals
  have valueRetained := valueFresh.after (dead_lowerBound lo) lowRun
  apply RhsOperandsAt.bindRun (hiChild env lowered lowerBound)
  intro high after highRun
  have valueRetained := valueRetained.after (dead_lowerBound hi) highRun
  apply RhsOperandsAt.emitDef
  intro live used member
  simp only [Op.uses, List.mem_cons, List.mem_append] at member
  rcases member with rfl | lowMember | highMember
  · exact valueRetained live
  · exact Nat.le_trans viewedBound (freshValues_lowerBound lo lowRun
      (live_before (dead_lowerBound hi) highRun live) used lowMember)
  · exact Nat.le_trans lowerBound (freshValues_lowerBound hi highRun live used highMember)

theorem rhsOperands_bound {floor : Nat} (expression : Expr)
    (child : RhsOperandsRun floor (lowerExpr expression)) (fromEnd : Bool) :
    RhsOperandsRun floor (lowerBound (if fromEnd then .fromEnd expression else .expr expression)) := by
  cases fromEnd <;> intro env before bound <;> simp only [Bool.false_eq_true, ↓reduceIte, lowerBound]
  all_goals exact (child env before bound).bind (RhsOperandsAt.pure _ _ _ _)

theorem rhsOperands_borrowArg (floor : Nat) (mu : Mutability) (place : Place)
    (child : RhsOperandsRun floor (lowerPlace place)) :
    RhsOperandsRun floor (lowerArg (.byRef mu place)) := by
  intro env before bound
  simp only [lowerArg]
  apply RhsOperandsAt.bindFresh bound (child env before bound)
    (advB_lowerPlace place) (freshValue_lowerPlace place)
  intro value middle _ _ valueFresh
  exact RhsOperandsAt.borrowTo _ _ _ _ _ valueFresh

theorem rhsOperands_eachSource (floor : Nat) (view : View)
    (placeChild : ∀ place, view = .of place → RhsOperandsRun floor (lowerPlace place))
    (expressionChild : ∀ expr, view = .val expr → RhsOperandsRun floor (lowerExpr expr)) :
    RhsOperandsRun floor (lowerEachSource view) := by
  cases view with
  | of place =>
    intro env before bound
    simp only [lowerEachSource]
    apply RhsOperandsAt.bindFresh bound (placeChild place rfl env before bound)
      (advB_lowerPlace place) (freshValue_lowerPlace place)
    intro value middle _ _ valueFresh
    apply (RhsOperandsAt.emitDef floor env middle _ ?_).bind
    · exact RhsOperandsAt.pure _ _ _ _
    · simpa only [Op.uses, List.mem_singleton] using
        fun live used equal => equal ▸ valueFresh live

  | val expression =>
    intro env before bound
    simp only [lowerEachSource]
    apply RhsOperandsAt.bindFresh bound (expressionChild expression rfl env before bound)
      (advB_lowerExpr expression) (freshValue_lowerExpr expression)
    intro value middle _ _ valueFresh
    apply (RhsOperandsAt.emitDef floor env middle (.sliceView value) ?_).bind
    · exact RhsOperandsAt.pure _ _ _ _
    · simpa only [Op.uses, List.mem_singleton] using
        fun live used equal => equal ▸ valueFresh live

end Goose.Lower.Validation
