import Goose.Lower.Validation.ReplacementEmissionEvidence
import Goose.Lower.Validation.ReplacementScopedDefinitions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmitsOnly.fresh_definition {property : Inst → Prop} {before captured finalState : LS}
    {func : Func} {block : GIR.Block} {value : ValueId} {op : Op}
    (emitted : EmitsOnly property before captured)
    (initialDense : before.DenseDefinitions) (capturedDense : captured.DenseDefinitions)
    (finalDense : finalState.DenseDefinitions) (extension : captured.Ext finalState)
    (blocks : func.blocks = finishBlocks finalState.blocks)
    (member : block ∈ func.blocks.toList) (defined : Inst.def value op ∈ block.insts)
    (lower : before.vals.size ≤ value) (upper : value < captured.vals.size) :
    property (.def value op) := by
  have initialExtension : before.Ext captured := by
    refine ⟨emitted.blocks,?_⟩
    intro index body row
    obtain ⟨next,nextAt,params,tail,append,_⟩ := emitted.old index body row
    exact ⟨next,nextAt,params,tail,append⟩
  obtain ⟨index,body,position,bodyAt,instruction,location⟩ := fresh_definition_site initialDense capturedDense
    finalDense initialExtension extension blocks member defined lower upper
  rcases location with fresh | ⟨initial,initialAt,positionLower⟩
  · exact emitted.fresh index body bodyAt fresh _ (List.mem_of_getElem? instruction)
  · obtain ⟨next,nextAt,_,tail,append,properties⟩ := emitted.old index initial initialAt
    have same : next = body := Option.some.inj (nextAt.symm.trans bodyAt)
    subst next
    rw [append,List.getElem?_append] at instruction
    have tailAt : tail[position - initial.insts.size]? = some (.def value op) := by
      simpa only [Array.length_toList,Nat.not_lt_of_ge positionLower,ite_false] using instruction
    exact properties _ (List.mem_of_getElem? tailAt)

#print axioms EmitsOnly.fresh_definition

end Goose.Lower.Validation
