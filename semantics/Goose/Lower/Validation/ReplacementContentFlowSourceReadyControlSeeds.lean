import Goose.Lower.Validation.ReplacementContentFlowSourceReadyBuilder

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.branchParameter {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed fragment : LS}
    {target : BlockId} {args : List ValueId} {body : BlockB} {parameter : ValueId × VTy} {argument : ValueId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : fragment.Ext completed)
    (branch : Inst.term (.br target args) ∈ fragment.insts)
    (targetRow : fragment.blocks[target]? = some body)
    (binding : (parameter, argument) ∈ body.params.zip args)
    (bounded : parameter.1 < state.values.size) (available : flowAt state.values argument ≠ .pending) :
    flowAt state.values parameter.1 ≠ .pending := by
  obtain ⟨finalBody, finalRow, parameters, _⟩ := extension.2 target body targetRow
  let finalBlock : GIR.Block := ⟨finalBody.params, finalBody.insts.toList⟩
  have finalTarget : func.blocks[target]? = some finalBlock := by
    rw [frame.blocks]
    simp only [finishBlocks, Array.getElem?_map, finalRow, Option.map_some]
    rfl
  have finalBinding : (parameter, argument) ∈ finalBlock.params.zip args := by
    simpa only [finalBlock, parameters] using binding
  have availableAfter := edge_parameter_ready finalTarget finalBinding bounded available
  have saturated := frame.fixed_instruction extension branch
  change edge func state target args = state at saturated
  rw [saturated] at availableAfter
  exact availableAfter

#print axioms SourceReadyFrame.branchParameter

end Goose.Lower.Validation.ReplacementContentFlowSource
