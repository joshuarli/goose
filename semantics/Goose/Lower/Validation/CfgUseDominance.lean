import Goose.Lower.Validation.CfgSemanticDominance

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Evidence

def DominatingUses (func : Func) : Prop :=
  ∀ block (bound : block < func.blocks.size) inst index,
    (inst, index) ∈ func.blocks[block].insts.zipIdx →
    ∀ value ∈ inst.uses,
      ∃ defining position, (cfgDefAt func)[value]? = some (some (defining, position)) ∧
        (if defining = block then position < (index : Int)
         else PathDominates (predecessors func) func.blocks.size block defining)

private theorem forIn_ok {items : List α} {body : α → PUnit → Check (ForInStep PUnit)}
    (accepted : ∀ item ∈ items, body item () = .ok (.yield ())) :
    forIn items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons, accepted item (by simp)]
    simp only [bind, Except.bind]
    exact ih fun next member => accepted next (by simp [member])

private theorem forIn'_ok {items : List α}
    {body : (item : α) → item ∈ items → PUnit → Check (ForInStep PUnit)}
    (accepted : ∀ item member, body item member () = .ok (.yield ())) :
    forIn' items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn'_cons, accepted item (by simp)]
    simp only [bind, Except.bind]
    exact ih fun next member => accepted next (by simp [member])

private theorem loop_done {loop : Check PUnit} {value : α}
    (checked : loop = .ok ()) : (loop >>= fun _ => pure value) = .ok value := by
  simp [checked, bind, Except.bind, pure, Except.pure]

theorem dominatingUses_checked (func : Func) (uses : DominatingUses func) (label : String) :
    cfgUseScan label func = .ok () := by
  unfold cfgUseScan
  apply loop_done
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply forIn'_ok
  intro block member
  have bound : block < func.blocks.size := by
    simpa [Std.Legacy.Range.size, List.mem_range'] using member
  apply loop_done
  apply forIn_ok
  intro pair present
  rcases pair with ⟨inst, index⟩
  apply loop_done
  apply forIn_ok
  intro value operand
  obtain ⟨defining, position, lookup, dominates⟩ := uses block bound inst index present value operand
  rw [lookup]
  by_cases same : defining = block
  · simp only [same, ite_true] at dominates ⊢
    simp [dominates, pure, Except.pure]
  · simp only [same, ite_false] at dominates ⊢
    have bit := dominators_contains_semantic func dominates
    simp [domBit] at bit
    simp [bit, pure, Except.pure]

end Goose.Lower.Validation
