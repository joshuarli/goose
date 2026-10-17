import Goose.Lower.Validation.ReplacementEmissionMap

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmitsOnly.inter {left right : Inst → Prop} {before after : LS}
    (one : EmitsOnly left before after) (two : EmitsOnly right before after) :
    EmitsOnly (fun inst => left inst ∧ right inst) before after := by
  refine ⟨one.blocks, ?_, ?_⟩
  · intro index body row
    obtain ⟨next, nextAt, params, tail, append, valid⟩ := one.old index body row
    obtain ⟨other, otherAt, _, otherTail, otherAppend, otherValid⟩ := two.old index body row
    have same : other = next := Option.some.inj (otherAt.symm.trans nextAt)
    subst other
    have sameTail : otherTail = tail := List.append_cancel_left (otherAppend.symm.trans append)
    subst otherTail
    exact ⟨next, nextAt, params, tail, append, fun inst member => ⟨valid inst member, otherValid inst member⟩⟩
  · intro index body row bound inst member
    exact ⟨one.fresh index body row bound inst member, two.fresh index body row bound inst member⟩

theorem finished_instruction_of_extension {before after : LS} {func : Func}
    (extension : before.Ext after) (blocks : func.blocks = finishBlocks after.blocks)
    {inst : Inst} (member : inst ∈ before.insts) :
    ∃ block ∈ func.blocks.toList, inst ∈ block.insts := by
  obtain ⟨body, bodyMember, instruction⟩ := List.mem_flatMap.mp (extension_inst_member extension member)
  refine ⟨cfgBlock body, ?_, instruction⟩
  rw [blocks, finishBlocks, Array.toList_map]
  exact List.mem_map.mpr ⟨body, bodyMember, rfl⟩

#print axioms EmitsOnly.inter
#print axioms finished_instruction_of_extension

end Goose.Lower.Validation
