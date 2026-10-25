import Goose.Lower.Validation.ReplacementDemandSitesCollected
import Goose.Lower.Validation.ReplacementDemandSitesOwners

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerContextAt_source_replacement_demand_sites {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {contextIndex : ContextId} {context : Context}
    (contextAt : module.contexts[contextIndex]? = some context) {impl : Core.Impl}
    (implAt : module.impls[context.impl]? = some impl)
    {blockIndex : Nat} {block : GIR.Block}
    (row : (lowerContextAt module context impl).blocks[blockIndex]? = some block)
    {position : Nat} {owner value : ValueId} {origin : Option OriginId}
    (present : block.insts[position]? = some (.eff (.replace owner value origin))) :
    ∃ sourceOrigin, origin = some sourceOrigin ∧
      ∃ site : ReplacementSiteAt (lowerEnv module impl.vars impl.results.toList)
        (cfg_implState module impl) blockIndex position owner value sourceOrigin,
        site.source.sourceRoot = .block impl.body ∧
        Nonempty (ReplacementDemandContext module contextIndex site.source.sourcePath
          site.source.place site.source.rhs sourceOrigin) := by
  obtain ⟨sourceOrigin, sameOrigin, site, rootEq⟩ :=
    (lowerImpl_replacement_sites accepted implAt).finishBlocks_sourceRoot rfl row present
  exact ⟨sourceOrigin, sameOrigin, site, rootEq,
    replacementDemandContext_forContext accepted contextAt implAt site.source rootEq⟩

theorem lowerGlobal_source_replacement_demand_sites {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {globalIndex : GlobalId} {global : Core.Global}
    (globalAt : module.globals[globalIndex]? = some global)
    {blockIndex : Nat} {block : GIR.Block}
    (row : (lowerGlobal module global).init.blocks[blockIndex]? = some block)
    {position : Nat} {owner value : ValueId} {origin : Option OriginId}
    (present : block.insts[position]? = some (.eff (.replace owner value origin))) :
    ∃ sourceOrigin, origin = some sourceOrigin ∧
      ∃ site : ReplacementSiteAt (lowerEnv module #[] [global.ty])
        (cfg_globalState module global) blockIndex position owner value sourceOrigin,
        site.source.sourceRoot = .expression global.init ∧
        Nonempty (ReplacementDemandContext module (module.contexts.size + globalIndex)
          site.source.sourcePath site.source.place site.source.rhs sourceOrigin) := by
  obtain ⟨sourceOrigin, sameOrigin, site, rootEq⟩ :=
    (lowerGlobal_replacement_sites accepted globalAt).finishBlocks_sourceRoot rfl row present
  exact ⟨sourceOrigin, sameOrigin, site, rootEq,
    replacementDemandContext_forGlobal accepted globalAt site.source rootEq⟩

#print axioms lowerContextAt_source_replacement_demand_sites
#print axioms lowerGlobal_source_replacement_demand_sites

end Goose.Lower.Validation
