import Goose.Lower.Validation.CfgBuilderEdges
import Goose.Lower.Validation.ReplacementContentFlowSourceInstructionTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem zip_swap (left : List α) (right : List β) :
    left.zip right = (right.zip left).map Prod.swap := by
  induction left generalizing right with
  | nil => simp
  | cons head tail ih =>
    cases right with
    | nil => simp
    | cons next rest => simp only [List.zip_cons_cons, List.map_cons, Prod.swap, ih]

theorem edgeTyped_of_arguments {completed : LS} {func : Func} {types : Array (Option VTy)}
    {target : BlockId} {arguments : List ValueId}
    (edge : EdgeArguments completed target arguments)
    (blocks : func.blocks = finishBlocks completed.blocks) (retained : types = completed.vals) :
    edgeTyped func types target arguments = true := by
  obtain ⟨body, row, arity, typed⟩ := edge
  have located : func.blocks[target]? = some ⟨body.params, body.insts.toList⟩ := by
    simp only [blocks, finishBlocks, Array.getElem?_map, row, Option.map_some]
  simp only [edgeTyped, located, Option.any_some, arity, beq_self_eq_true, Bool.true_and]
  rw [zip_swap arguments body.params, List.all_map]
  apply List.all_eq_true.mpr
  intro pair member
  rw [retained]
  exact beq_iff_eq.mpr (typed pair member)

theorem builderInstruction_edges {completed : LS} {func : Func}
    (edges : BuilderEdgeArguments completed)
    (blocks : func.blocks = finishBlocks completed.blocks)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {instruction : Inst} (instructionMember : instruction ∈ block.insts) :
    BuilderInstArguments completed instruction := by
  rw [blocks] at blockMember
  have mapped : block ∈ completed.blocks.toList.map (fun builder =>
      ({params := builder.params, insts := builder.insts.toList} : GIR.Block)) := by
    simpa only [finishBlocks, Array.toList_map] using blockMember
  obtain ⟨builder, builderMember, same⟩ := List.mem_map.mp mapped
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp builderMember)
  exact edges index builder row instruction (by simpa only [← same] using instructionMember)

theorem builderInstruction_model_edges {completed : LS} {func : Func} {types : Array (Option VTy)}
    (edges : BuilderEdgeArguments completed)
    (blocks : func.blocks = finishBlocks completed.blocks)
    (retained : types = completed.vals)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {instruction : Inst} (instructionMember : instruction ∈ block.insts) :
    (∀ target arguments, instruction = .term (.br target arguments) →
      edgeTyped func types target arguments = true) ∧
    (∀ condition yes yesArguments no noArguments,
      instruction = .term (.condbr condition yes yesArguments no noArguments) →
      edgeTyped func types yes yesArguments = true ∧ edgeTyped func types no noArguments = true) := by
  have actual := builderInstruction_edges edges blocks blockMember instructionMember
  constructor
  · intro target arguments same
    rw [same] at actual
    exact edgeTyped_of_arguments actual blocks retained
  · intro condition yes yesArguments no noArguments same
    rw [same] at actual
    exact ⟨edgeTyped_of_arguments actual.1 blocks retained,
      edgeTyped_of_arguments actual.2 blocks retained⟩

#print axioms edgeTyped_of_arguments
#print axioms builderInstruction_model_edges

end Goose.Lower.Validation.ReplacementContentFlowSource
