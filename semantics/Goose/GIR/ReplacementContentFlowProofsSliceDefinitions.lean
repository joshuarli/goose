import Goose.GIR.ReplacementContentFlowProofsSliceCallObservation
import Goose.Evidence.SSA

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem unique_definition_op {func : Func} {block other : Block} {value : ValueId} {op actual : Op}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (blockMember : block ∈ func.blocks.toList) (defined : Inst.def value op ∈ block.insts)
    (otherMember : other ∈ func.blocks.toList) (actualAt : Inst.def value actual ∈ other.insts) : actual = op := by
  rw [← definitionEntries_ids_func] at unique
  have same := entry_eq_of_nodup_ids unique
    (definitionEntry_mem (by simpa using otherMember) actualAt)
    (definitionEntry_mem (by simpa using blockMember) defined) rfl
  exact Option.some.inj (congrArg Prod.snd same)

theorem unique_definition_not_parameter {func : Func} {block : Block} {value : ValueId} {op : Op}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (blockMember : block ∈ func.blocks.toList) (defined : Inst.def value op ∈ block.insts) :
    ∀ other ∈ func.blocks.toList, value ∉ other.params.map Prod.fst := by
  rw [← definitionEntries_ids_func] at unique
  intro other otherMember parameter
  have same := entry_eq_of_nodup_ids unique
    (definitionEntry_mem (by simpa using blockMember) defined)
    (parameterEntry_mem (by simpa using otherMember) parameter) rfl
  cases same

#print axioms unique_definition_op
#print axioms unique_definition_not_parameter

end Goose.GIR.ReplacementContentFlow.Model
