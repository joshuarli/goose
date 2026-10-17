import Goose.Lower.Validation.DefinitionSites

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem fresh_definition_site {before captured finalState : LS}
    {func : Func} {block : GIR.Block} {value : ValueId} {op : Op}
    (initialDense : before.DenseDefinitions) (capturedDense : captured.DenseDefinitions)
    (finalDense : finalState.DenseDefinitions) (initialExtension : before.Ext captured)
    (extension : captured.Ext finalState) (blocks : func.blocks = finishBlocks finalState.blocks)
    (member : block ∈ func.blocks.toList) (defined : Inst.def value op ∈ block.insts)
    (lower : before.vals.size ≤ value) (upper : value < captured.vals.size) :
    ∃ index body position, captured.blocks[index]? = some body ∧
      body.insts.toList[position]? = some (.def value op) ∧
      (before.blocks.size ≤ index ∨
        ∃ initial, before.blocks[index]? = some initial ∧ initial.insts.size ≤ position) := by
  rw [blocks,finishBlocks,Array.toList_map] at member
  obtain ⟨body,bodyMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨index,bodyAt⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp bodyMember)
  obtain ⟨position,positionAt⟩ := List.mem_iff_getElem?.mp defined
  obtain ⟨old,oldAt,oldInstruction⟩ := old_instruction_site capturedDense finalDense extension bodyAt positionAt upper
  refine ⟨index,old,position,oldAt,oldInstruction,?_⟩
  by_cases previous : index < before.blocks.size
  · let initial := before.blocks[index]
    have initialAt : before.blocks[index]? = some initial := by simp [initial,previous]
    obtain ⟨next,nextAt,_,tail,append⟩ := initialExtension.2 index initial initialAt
    have same : next = old := Option.some.inj (nextAt.symm.trans oldAt)
    subst next
    apply Or.inr
    refine ⟨initial,initialAt,?_⟩
    by_cases early : initial.insts.size ≤ position
    · exact early
    · exfalso
      have bound : position < initial.insts.toList.length := by simpa using Nat.lt_of_not_ge early
      have initialInstruction : initial.insts.toList[position]? = some (.def value op) := by
        rw [append,List.getElem?_append_left bound] at oldInstruction
        exact oldInstruction
      have inDefs : value ∈ before.defs := by
        apply List.mem_flatMap.mpr
        refine ⟨initial,Array.mem_toList_iff.mpr (Array.mem_of_getElem? initialAt),?_⟩
        simp only [BlockB.defs,List.mem_append,List.mem_filterMap]
        exact Or.inr ⟨.def value op,List.mem_of_getElem? initialInstruction,rfl⟩
      have oldBound : value < before.vals.size := List.mem_range.mp (initialDense.subset inDefs)
      exact Nat.not_le_of_lt oldBound lower
  · exact Or.inl (Nat.le_of_not_gt previous)

theorem fresh_parameter_target {before captured finalState : LS}
    {func : Func} {block : GIR.Block} {target position value : Nat} {type : VTy}
    (initialDense : before.DenseDefinitions) (capturedDense : captured.DenseDefinitions)
    (finalDense : finalState.DenseDefinitions) (initialExtension : before.Ext captured)
    (extension : captured.Ext finalState) (blocks : func.blocks = finishBlocks finalState.blocks)
    (targetAt : func.blocks[target]? = some block) (parameterAt : block.params[position]? = some (value,type))
    (lower : before.vals.size ≤ value) (upper : value < captured.vals.size) :
    ∃ body, captured.blocks[target]? = some body ∧ body.params[position]? = some (value,type) ∧
      before.blocks.size ≤ target ∧ target < captured.blocks.size := by
  rw [blocks,finishBlocks,Array.getElem?_map] at targetAt
  cases finalAt : finalState.blocks[target]? with
  | none => simp [finalAt] at targetAt
  | some body =>
      simp only [finalAt,Option.map_some,Option.some.injEq] at targetAt
      subst block
      obtain ⟨old,oldAt,oldParameter⟩ := old_parameter_site capturedDense finalDense extension finalAt parameterAt upper
      refine ⟨old,oldAt,oldParameter,?_,(Array.getElem?_eq_some_iff.mp oldAt).1⟩
      by_cases previous : target < before.blocks.size
      · let initial := before.blocks[target]
        have initialAt : before.blocks[target]? = some initial := by simp [initial,previous]
        obtain ⟨next,nextAt,params,_,_⟩ := initialExtension.2 target initial initialAt
        have same : next = old := Option.some.inj (nextAt.symm.trans oldAt)
        subst next
        rw [params] at oldParameter
        have inDefs : value ∈ before.defs := by
          apply List.mem_flatMap.mpr
          refine ⟨initial,Array.mem_toList_iff.mpr (Array.mem_of_getElem? initialAt),?_⟩
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨(value,type),List.mem_of_getElem? oldParameter,rfl⟩
        have oldBound : value < before.vals.size := List.mem_range.mp (initialDense.subset inDefs)
        exact False.elim (Nat.not_le_of_lt oldBound lower)
      · exact Nat.le_of_not_gt previous

#print axioms fresh_definition_site
#print axioms fresh_parameter_target

end Goose.Lower.Validation
