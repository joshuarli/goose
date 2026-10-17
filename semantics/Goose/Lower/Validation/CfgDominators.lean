import Goose.Evidence.Dominance

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Evidence

structure DominanceRelation (preds : Array (List BlockId)) (size : Nat)
    (dominates : BlockId → BlockId → Prop) : Prop where
  bounds : ∀ block parent, dominates block parent → block < size ∧ parent < size
  entry : ∀ parent, dominates 0 parent → parent = 0
  predecessors : ∀ block parent, dominates block parent → block ≠ 0 → block ≠ parent →
    ∀ prior ∈ preds[block]?.getD [], dominates prior parent

def MasksContain (dominates : BlockId → BlockId → Prop) (masks : Array Nat) : Prop :=
  ∀ block parent, dominates block parent → domBit masks block parent = true

theorem intersection_contains {masks : Array Nat} {parents : List BlockId} {full parent : Nat}
    (initial : full.testBit parent = true)
    (allParents : ∀ prior ∈ parents, domBit masks prior parent = true) :
    (parents.foldl (fun mask prior => mask &&& (masks[prior]?.getD 0)) full).testBit parent = true := by
  induction parents generalizing full with
  | nil => exact initial
  | cons prior rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · simpa only [Nat.testBit_and, initial, Bool.true_and, domBit] using allParents prior (by simp)
    · intro next member
      exact allParents next (by simp [member])

theorem domUpdate_contains {preds : Array (List BlockId)} {size full : Nat}
    {dominates : BlockId → BlockId → Prop} (relation : DominanceRelation preds size dominates)
    (fullBits : ∀ parent < size, full.testBit parent = true)
    {state : Array Nat × Bool} (masksSize : state.1.size = size)
    (contains : MasksContain dominates state.1) (changed : BlockId) :
    MasksContain dominates (domUpdate preds full state changed).1 := by
  intro block parent related
  by_cases equal : changed = block
  · subst changed
    by_cases isEntry : block = 0
    · simp only [domUpdate, isEntry, ite_true]
      simpa only [isEntry] using contains block parent related
    · have bounds := relation.bounds block parent related
      rw [domUpdate_bit_at (by simpa [masksSize] using bounds.1) isEntry]
      by_cases same : block = parent
      · subst parent
        simp [Nat.testBit_or, Nat.testBit_shiftLeft]
      · have every := relation.predecessors block parent related isEntry same
        have intersection := intersection_contains (fullBits parent bounds.2)
          (fun prior member => contains prior parent (every prior member))
        simp [Nat.testBit_or, intersection]
  · rw [domUpdate_bit_ne equal]
    exact contains block parent related

theorem domScan_contains {preds : Array (List BlockId)} {size full : Nat}
    {dominates : BlockId → BlockId → Prop} (relation : DominanceRelation preds size dominates)
    (fullBits : ∀ parent < size, full.testBit parent = true)
    (blocks : List BlockId) (state : Array Nat × Bool) (masksSize : state.1.size = size)
    (contains : MasksContain dominates state.1) :
    (blocks.foldl (domUpdate preds full) state).1.size = size ∧
      MasksContain dominates (blocks.foldl (domUpdate preds full) state).1 := by
  induction blocks generalizing state with
  | nil => exact ⟨masksSize, contains⟩
  | cons block rest ih =>
    rw [List.foldl_cons]
    exact ih _ ((domUpdate_size state block).trans masksSize)
      (domUpdate_contains relation fullBits masksSize contains block)

theorem domRound_contains {preds : Array (List BlockId)} {size full : Nat}
    {dominates : BlockId → BlockId → Prop} (relation : DominanceRelation preds size dominates)
    (fullBits : ∀ parent < size, full.testBit parent = true)
    {masks : Array Nat} (masksSize : masks.size = size) (contains : MasksContain dominates masks) :
    (domRound preds size full masks).1.size = size ∧
      MasksContain dominates (domRound preds size full masks).1 :=
  domScan_contains relation fullBits (List.range size) (masks, false) masksSize contains

theorem dominators_go_contains {preds : Array (List BlockId)} {size full : Nat}
    {dominates : BlockId → BlockId → Prop} (relation : DominanceRelation preds size dominates)
    (fullBits : ∀ parent < size, full.testBit parent = true) (fuel : Nat)
    {masks : Array Nat} (masksSize : masks.size = size) (contains : MasksContain dominates masks) :
    MasksContain dominates (dominators.go preds size full fuel masks) := by
  induction fuel generalizing masks with
  | zero => exact contains
  | succ fuel ih =>
    change MasksContain dominates
      (if (domRound preds size full masks).2 then
        dominators.go preds size full fuel (domRound preds size full masks).1
      else (domRound preds size full masks).1)
    obtain ⟨sizeNext, containsNext⟩ := domRound_contains relation fullBits masksSize contains
    split
    · exact ih sizeNext containsNext
    · exact containsNext

theorem dominators_contains (func : Func) (preds : Array (List BlockId))
    {dominates : BlockId → BlockId → Prop}
    (relation : DominanceRelation preds func.blocks.size dominates) :
    MasksContain dominates (dominators func preds) := by
  let full := (1 <<< func.blocks.size) - 1
  have fullBits : ∀ parent < func.blocks.size, full.testBit parent = true := by
    intro parent bound
    simp [full, Nat.shiftLeft_eq, bound]
  apply dominators_go_contains relation fullBits (func.blocks.size + 2) (by simp)
  intro block parent related
  have bounds := relation.bounds block parent related
  by_cases isEntry : block = 0
  · subst block
    have parentEntry := relation.entry parent related
    subst parent
    have initialBound : 0 < (Array.replicate func.blocks.size full).size := by simpa using bounds.1
    simp [domBit, Array.set!_eq_setIfInBounds, bounds.1]
  · simp only [domBit, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (Ne.symm isEntry)]
    simp only [Array.getElem?_replicate, bounds.1, ite_true, Option.getD_some]
    exact fullBits parent bounds.2

end Goose.Lower.Validation
