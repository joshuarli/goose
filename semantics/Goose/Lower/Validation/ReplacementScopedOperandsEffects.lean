import Goose.Lower.Validation.ReplacementScopedOperandsSites

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem rhsOperands_unaryEffect {floor : Nat} {action : B ValueId}
    (operand : RhsOperandsRun floor action) (advance : AdvB action) (fresh : FreshValueRun action)
    (effect : ValueId → Effect) (uses : ∀ value, (effect value).uses ⊆ [value]) :
    RhsOperandsRun floor (do let value ← action; emitEffect (effect value)) := by
  intro env before bound
  apply RhsOperandsAt.bindFresh bound (operand env before bound) advance fresh
  intro value middle _ _ valueFresh
  exact RhsOperandsAt.emitEffect floor env middle (effect value) fun live used member =>
    (List.mem_singleton.mp (uses value member)) ▸ (valueFresh live)

theorem rhsOperands_binaryEffect {floor : Nat} {first second : B ValueId}
    (one : RhsOperandsRun floor first) (two : RhsOperandsRun floor second)
    (advanceOne : AdvB first) (advanceTwo : AdvB second)
    (freshOne : FreshValueRun first) (freshTwo : FreshValueRun second) (deadTwo : DeadRun second)
    (effect : ValueId → ValueId → Effect)
    (uses : ∀ left right, (effect left right).uses ⊆ [left, right]) :
    RhsOperandsRun floor (do let left ← first; let right ← second; emitEffect (effect left right)) := by
  intro env before bound
  apply RhsOperandsAt.bindFresh bound (one env before bound) advanceOne freshOne
  intro left middle _ middleBound leftFresh
  apply RhsOperandsAt.bindFresh middleBound (two env middle middleBound) advanceTwo freshTwo
  intro right after rightRun _ rightFresh
  have retained := leftFresh.after deadTwo rightRun
  apply RhsOperandsAt.emitEffect
  intro live source member
  have selected := uses left right member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl
  · exact retained live
  · exact rightFresh live

theorem rhsOperands_coerceSlot (floor : Nat) (slot : SlotId) (expr : Expr) (origin : OriginId)
    (child : RhsOperandsRun floor (lowerExpr expr)) :
    RhsOperandsRun floor (do let value ← lowerExpr expr; coerceSlot slot value origin) := by
  intro env before bound
  apply RhsOperandsAt.bindFresh bound (child env before bound) (advB_lowerExpr expr) (freshValue_lowerExpr expr)
  intro value middle _ middleBound valueFresh
  exact RhsOperandsAt.coerceSlot _ _ _ _ _ _ middleBound valueFresh

theorem freshValue_coerceSlot (slot : SlotId) (expr : Expr) (origin : OriginId) :
    FreshValueRun (do let value ← lowerExpr expr; coerceSlot slot value origin) := by
  intro env before result after run live
  obtain ⟨value, middle, first, last⟩ := bind_eq.mp run
  have fresh := RhsValueFresh.output (Nat.le_refl before.vals.size) (freshValue_lowerExpr expr) first
  exact RhsValueFresh.coerceSlot (advB_lowerExpr expr env before value middle first).vals fresh last live

end Goose.Lower.Validation
