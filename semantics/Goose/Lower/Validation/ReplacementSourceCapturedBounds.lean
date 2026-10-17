import Goose.Lower.Validation.ReplacementSourceOperandBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem extension_definition_ids_subset {before after : LS} (extension : before.Ext after) :
    before.defs ⊆ after.defs := by
  intro value member
  obtain ⟨body, bodyMember, definition⟩ := List.mem_flatMap.mp member
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp bodyMember)
  obtain ⟨next, nextAt, params, tail, append⟩ := extension.2 index body row
  apply List.mem_flatMap.mpr
  refine ⟨next, Array.mem_toList_iff.mpr (Array.mem_of_getElem? nextAt), ?_⟩
  simp only [BlockB.defs, List.mem_append] at definition ⊢
  rcases definition with parameter | instruction
  · exact Or.inl (params ▸ parameter)
  · apply Or.inr
    rw [append, List.filterMap_append]
    exact List.mem_append_left _ instruction

theorem extension_dense_values_le {before after : LS} (extension : before.Ext after)
    (initial : before.DenseDefinitions) (final : after.DenseDefinitions) :
    before.vals.size ≤ after.vals.size := by
  have unique := initial.nodup_iff.mpr List.nodup_range
  have count := unique.length_le_of_subset (extension_definition_ids_subset extension)
  simpa only [initial.length, final.length, List.length_range] using count

theorem AcceptedReplacementSite.captured_numValues_le {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite le state owner value origin)
    {func : Func} (blocks : func.blocks = finishBlocks state.blocks)
    (dense : state.DenseDefinitions) : site.site.captured.vals.size ≤ func.numValues := by
  rw [← dense_values_eq_numValues dense blocks]
  exact extension_dense_values_le site.captured_extension site.captured_generated.dense dense

#print axioms extension_definition_ids_subset
#print axioms extension_dense_values_le
#print axioms AcceptedReplacementSite.captured_numValues_le

end Goose.Lower.Validation
