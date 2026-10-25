import Goose.Lower.Validation.ReplacementScopedOperandsBlocks
import Goose.Lower.Validation.ReplacementScopedDefinitions
import Goose.Lower.Validation.OperandBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmitsOnly.instruction_after_prefix {property : Inst → Prop} {before after : LS}
    (emitted : EmitsOnly property before after) {index position : Nat} {body : BlockB} {instruction : Inst}
    (bodyAt : after.blocks[index]? = some body) (instructionAt : body.insts.toList[position]? = some instruction)
    (location : before.blocks.size ≤ index ∨
      ∃ initial, before.blocks[index]? = some initial ∧ initial.insts.size ≤ position) :
    property instruction := by
  rcases location with fresh | ⟨initial, initialAt, lower⟩
  · exact emitted.fresh index body bodyAt fresh instruction (List.mem_of_getElem? instructionAt)
  · obtain ⟨next, nextAt, _, tail, append, properties⟩ := emitted.old index initial initialAt
    have same : next = body := Option.some.inj (nextAt.symm.trans bodyAt)
    subst next
    rw [append] at instructionAt
    have initialLength : initial.insts.toList.length ≤ position := by simpa using lower
    rw [List.getElem?_append_right initialLength] at instructionAt
    exact properties instruction (List.mem_of_getElem? instructionAt)

theorem scoped_definition_operand_bounds {before captured finalState : LS}
    {func : Func} {block : GIR.Block} {value : ValueId} {op : Op}
    (initialDense : before.DenseDefinitions) (capturedDense : captured.DenseDefinitions)
    (finalDense : finalState.DenseDefinitions) (initialExtension : before.Ext captured)
    (extension : captured.Ext finalState) (blocks : func.blocks = finishBlocks finalState.blocks)
    (emitted : EmitsOnly (RhsUsesFresh before.vals.size) before captured)
    (capturedOperands : OperandBounds captured)
    (member : block ∈ func.blocks.toList) (defined : Inst.def value op ∈ block.insts)
    (lower : before.vals.size ≤ value) (upper : value < captured.vals.size) :
    ∀ source ∈ (Inst.def value op).uses, before.vals.size ≤ source ∧ source < captured.vals.size := by
  obtain ⟨index, body, position, bodyAt, instructionAt, location⟩ :=
    fresh_definition_site initialDense capturedDense finalDense initialExtension extension blocks member defined lower upper
  have fresh := emitted.instruction_after_prefix bodyAt instructionAt location
  have instructionMember : Inst.def value op ∈ captured.insts := by
    unfold LS.insts
    apply List.mem_flatMap.mpr
    exact ⟨body, Array.mem_toList_iff.mpr (Array.mem_of_getElem? bodyAt), List.mem_of_getElem? instructionAt⟩
  intro source used
  exact ⟨fresh source used, capturedOperands.uses _ instructionMember source used⟩

theorem EmitsOnly.term_to_fresh_target {property : Inst → Prop} {before captured : LS}
    (emitted : EmitsOnly property before captured) (targets : TargetsBounded before)
    {source target : BlockId} {body : BlockB} {term : Term}
    (row : captured.blocks[source]? = some body) (member : Inst.term term ∈ body.insts.toList)
    (successor : target ∈ term.successors) (freshTarget : before.blocks.size ≤ target) :
    property (.term term) := by
  by_cases old : source < before.blocks.size
  · let initial := before.blocks[source]
    have initialAt : before.blocks[source]? = some initial := by simp [initial, old]
    obtain ⟨next, nextAt, _, tail, append, properties⟩ := emitted.old source initial initialAt
    have same : next = body := Option.some.inj (nextAt.symm.trans row)
    subst next
    rw [append] at member
    rcases List.mem_append.mp member with previous | added
    · have termMember : term ∈ (cfgBlock initial).terms :=
        List.mem_filterMap.mpr ⟨.term term, previous, rfl⟩
      have bound := targets source initial initialAt target
        (List.mem_flatMap.mpr ⟨term, termMember, successor⟩)
      exact False.elim (Nat.not_lt_of_ge freshTarget bound)
    · exact properties _ added
  · exact emitted.fresh source body row (Nat.le_of_not_gt old) _ member

theorem scoped_incoming_operand_bounds {before captured finalState : LS}
    {func : Func} {parameterBlock sourceBlock : GIR.Block}
    {target parameterIndex value : Nat} {type : VTy} {term : Term}
    (initialDense : before.DenseDefinitions) (capturedDense : captured.DenseDefinitions)
    (finalDense : finalState.DenseDefinitions) (initialExtension : before.Ext captured)
    (extension : captured.Ext finalState) (blocks : func.blocks = finishBlocks finalState.blocks)
    (emitted : EmitsOnly (RhsUsesFresh before.vals.size) before captured)
    (capturedOperands : OperandBounds captured) (initialTargets : TargetsBounded before)
    (framed : IntervalEdgesFramed before captured finalState)
    (targetAt : func.blocks[target]? = some parameterBlock)
    (parameterAt : parameterBlock.params[parameterIndex]? = some (value, type))
    (lower : before.vals.size ≤ value) (upper : value < captured.vals.size)
    (sourceMember : sourceBlock ∈ func.blocks.toList) (termMember : Inst.term term ∈ sourceBlock.insts)
    (successor : target ∈ term.successors) :
    ∀ source ∈ term.uses, before.vals.size ≤ source ∧ source < captured.vals.size := by
  obtain ⟨parameterBody, _, _, freshTarget, targetBound⟩ := fresh_parameter_target initialDense
    capturedDense finalDense initialExtension extension blocks targetAt parameterAt lower upper
  obtain ⟨sourceIndex, sourceAt⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp sourceMember)
  rw [blocks, finishBlocks, Array.getElem?_map] at sourceAt
  cases bodyAt : finalState.blocks[sourceIndex]? with
  | none => simp [bodyAt] at sourceAt
  | some body =>
    simp only [bodyAt, Option.map_some, Option.some.injEq] at sourceAt
    subst sourceBlock
    obtain ⟨old, oldAt, oldTerm⟩ := framed sourceIndex body term target bodyAt termMember
      successor freshTarget targetBound
    have fresh := emitted.term_to_fresh_target initialTargets oldAt oldTerm successor freshTarget
    have instructionMember : Inst.term term ∈ captured.insts := by
      unfold LS.insts
      apply List.mem_flatMap.mpr
      exact ⟨old, Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldAt), oldTerm⟩
    intro source used
    exact ⟨fresh source used, capturedOperands.uses _ instructionMember source used⟩

end Goose.Lower.Validation
