import Goose.Lower.Validation.ReplacementScopedOperandsCoercions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def RhsOperandsRun (floor : Nat) (action : B α) : Prop :=
  ∀ env before, floor ≤ before.vals.size → RhsOperandsAt floor env before action

theorem RhsOperandsAt.bindRun {floor : Nat} {env : LEnv} {before : LS}
    {first : B α} {next : α → B β} (one : RhsOperandsAt floor env before first)
    (two : ∀ value middle, first env before = (value, middle) →
      RhsOperandsAt floor env middle (next value)) :
    RhsOperandsAt floor env before (first >>= next) :=
  one.bind (two _ _ rfl)

theorem RhsOperandsAt.bindFresh {floor : Nat} {env : LEnv} {before : LS}
    {first : B ValueId} {next : ValueId → B α}
    (floorBound : floor ≤ before.vals.size) (one : RhsOperandsAt floor env before first)
    (advance : AdvB first) (fresh : FreshValueRun first)
    (two : ∀ value middle, first env before = (value, middle) →
      floor ≤ middle.vals.size → RhsValueFresh floor middle value →
      RhsOperandsAt floor env middle (next value)) :
    RhsOperandsAt floor env before (first >>= next) := by
  apply one.bindRun
  intro value middle run
  exact two value middle run (Nat.le_trans floorBound (advance env before value middle run).vals)
    (RhsValueFresh.output floorBound fresh run)

theorem RhsOperandsAt.bindUnchanged {floor : Nat} {env : LEnv} {before : LS}
    {first : B α} {next : α → B β}
    (same : ∀ env state, (first env state).2 = state)
    (two : ∀ value, RhsOperandsAt floor env before (next value)) :
    RhsOperandsAt floor env before (first >>= next) := by
  apply RhsOperandsAt.bindRun (RhsOperandsAt.of_blocks (congrArg LS.blocks (same env before)))
  intro value middle run
  have unchanged := same env before
  rw [run] at unchanged
  change middle = before at unchanged
  subst middle
  exact two value

theorem rhsOperands_unary {floor : Nat} {action : B ValueId}
    (operand : RhsOperandsRun floor action) (advance : AdvB action) (fresh : FreshValueRun action)
    (op : ValueId → Op) (uses : ∀ value, (op value).uses ⊆ [value]) :
    RhsOperandsRun floor (do let value ← action; emitDef (op value)) := by
  intro env before floorBound
  apply RhsOperandsAt.bindFresh floorBound (operand env before floorBound) advance fresh
  intro value middle run bound valueFresh
  exact RhsOperandsAt.emitDef floor env middle (op value) fun live source member => by
    have equal : source = value := List.mem_singleton.mp (uses value member)
    exact equal ▸ valueFresh live

theorem rhsOperands_binary {floor : Nat} {first second : B ValueId}
    (one : RhsOperandsRun floor first) (two : RhsOperandsRun floor second)
    (advanceOne : AdvB first) (advanceTwo : AdvB second)
    (freshOne : FreshValueRun first) (freshTwo : FreshValueRun second) (deadTwo : DeadRun second)
    (op : ValueId → ValueId → Op) (uses : ∀ left right, (op left right).uses ⊆ [left, right]) :
    RhsOperandsRun floor (do let left ← first; let right ← second; emitDef (op left right)) := by
  intro env before floorBound
  apply RhsOperandsAt.bindFresh floorBound (one env before floorBound) advanceOne freshOne
  intro left middle leftRun middleBound leftFresh
  apply RhsOperandsAt.bindFresh middleBound (two env middle middleBound) advanceTwo freshTwo
  intro right after rightRun afterBound rightFresh
  have retained := leftFresh.after deadTwo rightRun
  apply RhsOperandsAt.emitDef
  intro live source member
  have selected := uses left right member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl
  · exact retained live
  · exact rightFresh live

theorem rhsOperands_emitDef (floor : Nat) (op : Op) (empty : op.uses = []) :
    RhsOperandsRun floor (emitDef op) := by
  intro env before _
  apply RhsOperandsAt.emitDef
  simp [empty]

end Goose.Lower.Validation
