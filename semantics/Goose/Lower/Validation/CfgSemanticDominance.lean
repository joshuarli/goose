import Goose.Lower.Validation.CfgDominators

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Evidence

def PathDominates (preds : Array (List BlockId)) (size : Nat)
    (block parent : BlockId) : Prop :=
  block < size ∧ parent < size ∧ ∀ length, ¬ PredWalk preds size parent length block

theorem PathDominates.self (preds : Array (List BlockId)) (size : Nat) (block : BlockId)
    (bound : block < size) : PathDominates preds size block block := by
  refine ⟨bound, bound, ?_⟩
  intro length walk
  exact walk.avoids rfl

theorem PathDominates.entry (preds : Array (List BlockId)) (size : Nat) (block : BlockId)
    (bound : block < size) : PathDominates preds size block 0 := by
  refine ⟨bound, Nat.zero_lt_of_lt bound, ?_⟩
  intro length walk
  induction walk with
  | entry _ avoids => exact avoids rfl
  | next prior _ _ _ ih => exact ih prior.bound

theorem pathDominates_relation (preds : Array (List BlockId)) (size : Nat)
    (bounds : ∀ block < size, ∀ prior ∈ preds[block]?.getD [], prior < size) :
    DominanceRelation preds size (PathDominates preds size) := by
  refine ⟨?_, ?_, ?_⟩
  · intro block parent related
    exact ⟨related.1, related.2.1⟩
  · intro parent related
    by_cases same : parent = 0
    · exact same
    · exact False.elim (related.2.2 0 (.entry related.1 (Ne.symm same)))
  · intro block parent related _ different prior member
    refine ⟨?_, related.2.1, ?_⟩
    · exact bounds block related.1 prior member
    · intro length walk
      exact related.2.2 (length + 1) (.next walk related.1 different member)

theorem predecessors_bounded (func : Func) :
    ∀ block : BlockId, ∀ prior ∈ (predecessors func)[block]?.getD [], prior < func.blocks.size := by
  let bounded := fun acc : Array (List BlockId) =>
    ∀ block : BlockId, ∀ prior ∈ acc[block]?.getD [], prior < func.blocks.size
  have modify {acc : Array (List BlockId)} (valid : bounded acc)
      (source : BlockId) (sourceBound : source < func.blocks.size) (target : BlockId) :
      bounded (acc.modify target (source :: ·)) := by
    intro block prior member
    simp only [Array.getElem?_modify] at member
    split at member
    · cases row : acc[block]? with
      | none => simp [row] at member
      | some parents =>
        simp only [row, Option.map_some, Option.getD_some, List.mem_cons] at member
        rcases member with rfl | member
        · exact sourceBound
        · exact valid block prior (by simpa [row] using member)
    · exact valid block prior member
  have inner (source : BlockId) (sourceBound : source < func.blocks.size)
      (targets : List BlockId) (acc : Array (List BlockId)) (valid : bounded acc) :
      bounded (targets.foldl (fun acc target =>
        if target < func.blocks.size then acc.modify target (source :: ·) else acc) acc) := by
    induction targets generalizing acc with
    | nil => exact valid
    | cons target rest ih =>
      rw [List.foldl_cons]
      apply ih
      split
      · exact modify valid source sourceBound target
      · exact valid
  have outer (sources : List BlockId) (sourceBounds : ∀ source ∈ sources, source < func.blocks.size)
      (acc : Array (List BlockId)) (valid : bounded acc) :
      bounded (sources.foldl (fun acc source => match func.blocks[source]? with
        | none => acc
        | some block => (block.terms.flatMap Term.successors).foldl (fun acc target =>
          if target < func.blocks.size then acc.modify target (source :: ·) else acc) acc) acc) := by
    induction sources generalizing acc with
    | nil => exact valid
    | cons source rest ih =>
      rw [List.foldl_cons]
      apply ih (fun next member => sourceBounds next (by simp [member]))
      cases row : func.blocks[source]? with
      | none => exact valid
      | some block => exact inner source (sourceBounds source (by simp)) _ acc valid
  apply outer (List.range func.blocks.size) (by simp)
  intro block prior member
  simp only [Array.getElem?_replicate] at member
  split at member <;> simp at member

theorem dominators_pathDominates (func : Func) (preds : Array (List BlockId))
    (bounds : ∀ block < func.blocks.size, ∀ prior ∈ preds[block]?.getD [], prior < func.blocks.size)
    {block parent : BlockId} (dominates : PathDominates preds func.blocks.size block parent) :
    domBit (dominators func preds) block parent = true :=
  dominators_contains func preds (pathDominates_relation preds func.blocks.size bounds) block parent dominates

theorem dominators_contains_semantic (func : Func) {block parent : BlockId}
    (dominates : PathDominates (predecessors func) func.blocks.size block parent) :
    domBit (dominators func (predecessors func)) block parent = true :=
  dominators_pathDominates func (predecessors func)
    (fun target _ source member => predecessors_bounded func target source member) dominates

end Goose.Lower.Validation
