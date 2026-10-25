import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContext
import Goose.Lower.Validation.SourceReplacementWriterLedgerShapes
import Goose.Lower.Validation.SourceOccurrenceReplacementSites

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

theorem canonical_context_replacement_occurrences_of_produced {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (produced : CanonicalContextOccurrenceReplayProduced module ctx impl
      (resultRoots (lower module) ((lower module).funcs.map fun func => func.valueTypes (lower module))))
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
          (.expression site.source.site.source.rhs) site.source.site.source.site.cleared := by
  obtain ⟨roots,range,after,upper,replayed,ready,returned,retained,ledger,sites⟩ := produced
  have below := ready.finished_provenance (cfg_context_blocks module ctx impl)
    (accepted_context_provenance_seed accepted contextRow implementationRow ready.slotsEq ready.recipes retained)
    (lower module).rootCount
  obtain ⟨sourceOrigin,originEq,site,loop,source⟩ := sites.finishBlocks rfl
    (contextInitial_instructions module impl) (cfg_context_blocks module ctx impl) blockAt instructionAt
  have same := Option.some.inj originEq
  subst sourceOrigin
  have located := contextReplay_statement_cursor source
  refine ⟨upper,by simpa only [module_implTypes_eq_native] using below,site,?_⟩
  have rhs := located.replacement_rhs
  simpa only [site.source.site.source.site.addressRun,site.source.site.source.site.clearRun] using rhs

#print axioms canonical_context_replacement_occurrences_of_produced

end Goose.Lower.Validation.SourceReplacementWriterLedger
