import Goose.Lower.Validation.SourceOccurrenceCanonicalAccepted
import Goose.Lower.Validation.ReplacementSourceSitesBuilder
import Goose.Lower.Validation.SummaryPreservationAcceptedSummaries

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

private theorem ledger_instruction {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {state : LS}
    (ledger : OccurrenceLedger env root func types upper initState state)
    (blocks : func.blocks = finishBlocks state.blocks)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {inst : Inst} (instMember : inst ∈ block.insts) :
    InstructionOccurrences env root func types upper inst := by
  have member := finishBlocks_instruction_member (blocks ▸ blockMember) instMember
  rcases ledger.members member with initial | occurrence
  · simp [initState, LS.insts] at initial
  · exact occurrence

theorem accepted_context_instruction_occurrences {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    ∃ upper, ProvenanceBelow
      ((lowerContextAt module ctx impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount) upper ∧
      ∀ block ∈ (lowerContextAt module ctx impl).blocks.toList, ∀ inst ∈ block.insts,
        InstructionOccurrences ⟨module, impl, ctx, []⟩ (.block impl.body)
          (lowerContextAt module ctx impl) ((lowerContextAt module ctx impl).valueTypes (lower module)) upper inst := by
  obtain ⟨roots, range, after, upper, replayed, ready, returned, retained, ledger, sites⟩ :=
    accepted_context_occurrence_replay_canonical accepted contextRow implementationRow
  have below := ready.finished_provenance (cfg_context_blocks module ctx impl)
    (accepted_context_provenance_seed accepted contextRow implementationRow ready.slotsEq ready.recipes retained)
    (lower module).rootCount
  exact ⟨upper, by simpa only [module_implTypes_eq_native] using below, fun _ member _ present => ledger_instruction ledger
    (cfg_context_blocks module ctx impl) member present⟩

theorem accepted_global_instruction_occurrences {module : Core.Module} {global : Core.Global}
    {index : GlobalId} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global) :
    ∃ upper, ProvenanceBelow
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) upper ∧
      ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ inst ∈ block.insts,
        InstructionOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init)
          (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper inst := by
  obtain ⟨roots, after, upper, replayed, ready, returned, ledger, sites⟩ :=
    accepted_global_occurrence_replay_canonical accepted globalRow
  have below := ready.finished_provenance (cfg_global_blocks module global)
    (global_provenance_seed module global _ upper ready.recipes) (lower module).rootCount
  exact ⟨upper, by simpa only [module_implTypes_eq_native] using below, fun _ member _ present => ledger_instruction ledger
    (cfg_global_blocks module global) member present⟩

end Goose.Lower.Validation.ReplacementContentFlowSource
