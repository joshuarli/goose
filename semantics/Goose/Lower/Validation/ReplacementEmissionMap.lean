import Goose.Lower.Validation.ReplacementEmission

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem extension_inst_member {before after : LS} (extension : before.Ext after)
    {inst : Inst} (member : inst ∈ before.insts) : inst ∈ after.insts := by
  obtain ⟨body, bodyMember, instMember⟩ := List.mem_flatMap.mp member
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp bodyMember)
  obtain ⟨next, nextAt, _, tail, append⟩ := extension.2 index body row
  apply List.mem_flatMap.mpr
  refine ⟨next, Array.mem_toList_iff.mpr (Array.mem_of_getElem? nextAt), ?_⟩
  rw [append]
  exact List.mem_append_left _ instMember

theorem EmitsOnly.map {property nextProperty : Inst → Prop} {before after : LS}
    (emitted : EmitsOnly property before after)
    (transform : ∀ inst ∈ after.insts, property inst → nextProperty inst) :
    EmitsOnly nextProperty before after := by
  refine ⟨emitted.blocks, ?_, ?_⟩
  · intro index body row
    obtain ⟨next, nextAt, params, tail, append, valid⟩ := emitted.old index body row
    refine ⟨next, nextAt, params, tail, append, ?_⟩
    intro inst member
    apply transform inst _ (valid inst member)
    apply List.mem_flatMap.mpr
    refine ⟨next, Array.mem_toList_iff.mpr (Array.mem_of_getElem? nextAt), ?_⟩
    rw [append]
    exact List.mem_append_right _ member
  · intro index body row lower inst member
    exact transform inst (List.mem_flatMap.mpr
      ⟨body, Array.mem_toList_iff.mpr (Array.mem_of_getElem? row), member⟩)
      (emitted.fresh index body row lower inst member)

end Goose.Lower.Validation
