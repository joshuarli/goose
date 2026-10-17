import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalFactory
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalInduction

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

theorem accepted_context_canonical_occurrence_replay_produced {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    CanonicalContextOccurrenceReplayProduced module ctx impl
      (resultRoots (lower module) ((lower module).funcs.map fun func => func.valueTypes (lower module))) := by
  apply canonical_context_occurrence_replay_produced_of_body accepted contextRow implementationRow
  intro roots range after replayed
  have source : SourceContextEnvironment (implEnv module impl) ⟨module, impl, ctx, []⟩ context :=
    ⟨accepted, ⟨rfl,rfl⟩,rfl,contextRow,implementationRow⟩
  have valid := SourceCanonicalRootFloors.sourceRootScopeValid_block
    (validate_implementation_checks accepted (Array.mem_toList_iff.mpr (Array.mem_of_getElem? implementationRow)))
  exact canonical_source_block_occurrence_replay impl.body source valid (accepted_resultRoots_below accepted)
    (accepted_context_scope_bounds accepted contextRow implementationRow) _ _ _ _ _

theorem accepted_context_canonical_replacement_occurrences {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    {index position owner value : Nat} {origin : OriginId} {block : GIR.Block}
    (blockAt : (lowerContextAt module ctx impl).blocks[index]? = some block)
    (instructionAt : block.insts[position]? = some (.eff (.replace owner value (some origin)))) :
    ∃ upper, ProvenanceBelow
      ((lowerContextAt module ctx impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount) upper ∧
      ∃ site : SiteOccurrences ⟨module, impl, ctx, []⟩ (.block impl.body) []
        (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
        (lowerContextAt module ctx impl) ((lowerContextAt module ctx impl).valueTypes (lower module))
        upper index position owner value origin,
        SourceLoweringAt (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
          (contextInitial module impl) (site.source.site.source.sourcePath ++ [1])
          (.expression site.source.site.source.rhs) site.source.site.source.site.cleared :=
  canonical_context_replacement_occurrences_of_produced accepted contextRow implementationRow
    (accepted_context_canonical_occurrence_replay_produced accepted contextRow implementationRow) blockAt instructionAt

#print axioms accepted_context_canonical_occurrence_replay_produced
#print axioms accepted_context_canonical_replacement_occurrences

end Goose.Lower.Validation.SourceReplacementWriterLedger
