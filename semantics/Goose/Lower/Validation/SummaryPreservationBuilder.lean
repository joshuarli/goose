import Goose.Lower.Validation.SummaryPreservationValueGrowth
import Goose.Lower.Validate
import Goose.Lower.Validation.SummaryPreservationFunctionShape

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem builder_parameter_bound {ls : LS} (dense : ls.DenseDefinitions)
    {block : BlockB} (member : block ∈ ls.blocks.toList)
    {pair : ValueId × VTy} (parameter : pair ∈ block.params) : pair.1 < ls.vals.size := by
  apply dense.mem_lt
  apply List.mem_flatMap.mpr
  refine ⟨block, member, ?_⟩
  simp only [BlockB.defs, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨pair, parameter, rfl⟩)

theorem builder_definition_bound {ls : LS} (dense : ls.DenseDefinitions)
    {result : ValueId} {op : Op} (member : Inst.def result op ∈ ls.insts) :
    result < ls.vals.size := by
  obtain ⟨block, blockMember, instructionMember⟩ := List.mem_flatMap.mp member
  apply dense.mem_lt
  apply List.mem_flatMap.mpr
  refine ⟨block, blockMember, ?_⟩
  simp only [BlockB.defs, List.mem_append]
  exact Or.inr (List.mem_filterMap.mpr ⟨.def result op, instructionMember, rfl⟩)

theorem builder_instruction_roots_after_push {res : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {upper : Prov} {newRoots : List RootRef}
    {ls : LS} {le : LEnv} {scopeCount : Nat}
    (symbols : ls.SymbolWF le scopeCount) (size : upper.vals.size = ls.vals.size)
    (blocks : func.blocks = finishBlocks ls.blocks)
    (closed : ∀ inst ∈ ls.insts, InstructionRootsClosed res vt func upper inst) :
    ∀ inst ∈ ls.insts,
      InstructionRootsClosed res vt func { upper with vals := upper.vals.push newRoots } inst := by
  intro inst member
  apply instruction_roots_closed_after_push (closed inst member)
  · intro value used
    rw [size]
    exact (symbols.instructions inst member).uses value used
  · intro result op equation
    rw [size]
    exact builder_definition_bound symbols.definitions (equation ▸ member)
  · intro block blockMember pair pairMember
    rw [blocks] at blockMember
    have origin : ∃ builder ∈ ls.blocks.toList,
        ({ params := builder.params, insts := builder.insts.toList } : Goose.GIR.Block) = block := by
      simpa [finishBlocks] using blockMember
    obtain ⟨builder, builderMember, equation⟩ := origin
    cases equation
    rw [size]
    exact builder_parameter_bound symbols.definitions builderMember pairMember


theorem appendInst_block_parameters (func : Func) (ls : LS) (block : BlockId) (inst : Inst) :
    BlockParametersAgree { func with blocks := finishBlocks ls.blocks }
      { func with blocks := finishBlocks (ls.appendInst block inst).blocks } := by
  intro target
  simp only [finishBlocks, LS.appendInst, Array.getElem?_map, Array.getElem?_modify]
  split <;> cases ls.blocks[target]? <;> rfl

end Goose.Lower.Validation.SummaryPreservation
