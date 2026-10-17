import Goose.Lower.Validation.SourceReadyCheckCalls
import Goose.Lower.Validation.SourceReadyStaticEdges
import Goose.Lower.Validation.SummaryPreservationReplayFinished

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.check_instruction (facts : SourceReadyFunction)
    (ready : SourceReadyBuilder facts.state facts.completed)
    (observed : ∀ instruction ∈ facts.completed.insts,
      ReadyCallObservations (lower facts.source.mod) facts.func facts.state instruction)
    (present : ∀ value, value < facts.func.numValues → ∃ type, facts.types[value]? = some (some type))
    (edges : BuilderEdgeArguments facts.completed)
    (retained : facts.types = facts.completed.vals)
    {block : GIR.Block} (member : block ∈ facts.func.blocks.toList)
    {instruction : Inst} (instructionMember : instruction ∈ block.insts)
    (native : checkInstTypes facts.func {(lower facts.source.mod).tyEnv facts.func with vals := facts.types}
      facts.types instruction = .ok ()) :
    checkInstruction (lower facts.source.mod) facts.func facts.types facts.state instruction = true := by
  have emitted := finishBlocks_instruction_member (facts.frame.blocks ▸ member) instructionMember
  have referenceReady : refReady facts.types facts.state instruction = true := by
    apply refReady_of_operands
    · intro value use
      exact present value (facts.native.uses block member instruction instructionMember value use)
    · intro value use reference
      exact (ready instruction emitted).1 value use
  have actualEdges := builderInstruction_model_edges edges facts.frame.blocks retained member instructionMember
  apply checkInstruction_of_native native referenceReady
  · intro value calleeId arguments origin same
    subst instruction
    exact facts.check_call_observed member instructionMember (observed _ emitted)
  · exact actualEdges.1
  · exact actualEdges.2

#print axioms SourceReadyFunction.check_instruction

end Goose.Lower.Validation.ReplacementContentFlowSource
