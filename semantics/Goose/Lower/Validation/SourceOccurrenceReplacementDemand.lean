import Goose.Lower.Validation.SourceOccurrenceReplacementSites
import Goose.Lower.Validation.ReplacementDemandSitesCollected

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

theorem accepted_context_replacement_demand_occurrences {module : Core.Module}
    {context : ContextId} {ctx : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[context]? = some ctx)
    (implAt : module.impls[ctx.impl]? = some impl)
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
        Nonempty (ReplacementDemandContext module context site.source.site.source.sourcePath
          site.source.site.source.place site.source.site.source.rhs origin) := by
  obtain ⟨upper, below, ⟨site⟩⟩ :=
    accepted_context_replacement_occurrences accepted contextAt implAt blockAt instructionAt
  exact ⟨upper, below, site, replacementDemandContext_forContext accepted contextAt implAt
    site.source.site.source site.source.root_eq⟩

theorem accepted_global_replacement_demand_occurrences {module : Core.Module}
    {index : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global)
    {blockIndex position owner value : Nat} {origin : OriginId} {block : GIR.Block}
    (blockAt : (lowerGlobal module global).init.blocks[blockIndex]? = some block)
    (instructionAt : block.insts[position]? = some (.eff (.replace owner value (some origin)))) :
    ∃ upper, ProvenanceBelow
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) upper ∧
      ∃ site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
        (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
        (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
        upper blockIndex position owner value origin,
        Nonempty (ReplacementDemandContext module (module.contexts.size + index)
          site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin) := by
  obtain ⟨upper, below, ⟨site⟩⟩ :=
    accepted_global_replacement_occurrences accepted globalAt blockAt instructionAt
  exact ⟨upper, below, site, replacementDemandContext_forGlobal accepted globalAt
    site.source.site.source site.source.root_eq⟩

#print axioms accepted_context_replacement_demand_occurrences
#print axioms accepted_global_replacement_demand_occurrences

end Goose.Lower.Validation.ReplacementContentFlowSource
