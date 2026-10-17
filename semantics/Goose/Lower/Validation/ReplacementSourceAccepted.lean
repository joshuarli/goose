import Goose.Lower.Validation.ReplacementSourceEntry
import Goose.Lower.Validation.SourceReplacementCallResultsApart
import Goose.Lower.Validation.CfgAcceptedModule
import Goose.Lower.Validation.SourceReplacementGlobalApart
import Goose.Lower.Validation.ValidationAcceptedStages
import Goose.Lower.Validation.SourceReplacementCanonicalApart
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalAccepted

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource SourceReplacementWriterLedger

private theorem lowerContextAt_checkShrinkReplace_of_canonical_occurrences {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {contextIndex : ContextId} {context : Context}
    (contextAt : module.contexts[contextIndex]? = some context) {impl : Core.Impl}
    (implAt : module.impls[context.impl]? = some impl)
    (canonical : ∀ {index position owner value : Nat} {origin : OriginId} {block : GIR.Block}
    (_blockAt : (lowerContextAt module context impl).blocks[index]? = some block)
    (_instructionAt : block.insts[position]? = some (.eff (.replace owner value (some origin)))),
    ∃ upper, ProvenanceBelow
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount) upper ∧
      ∃ site : SiteOccurrences ⟨module, impl, context, []⟩ (.block impl.body) []
        (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
        (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
        upper index position owner value origin,
        SourceLoweringAt (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
          (contextInitial module impl) (site.source.site.source.sourcePath ++ [1])
          (.expression site.source.site.source.rhs) site.source.site.source.site.cleared) (label : String) :
    checkShrinkReplace (lower module) label (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module)) = .ok () := by
  have builder := lowerImpl_emittedBuilder_of_accepted accepted implAt
  have graphs := lowerContext_mutableSnapshotGraphs_of_accepted (context := context) accepted implAt
  refine checkShrinkReplace_of_source_sites builder (cfg_context_blocks module context impl) rfl
    (lower_globalTypeTables module) (lower_signatureTables module) rfl rfl graphs
    (closedBlocks_of_finished (cfg_context_blocks module context impl) (lowerContextAt_terminators module context impl))
    (lowerImpl_blocks_nonempty module impl) ?_ ?_ label
  · intro index bounded
    exact lowerContextAt_emptyFacts_known module context impl _ _ bounded
  · intro index body row position owner value origin present
    have finalRow : (lowerContextAt module context impl).blocks[index]? = some (cfgBlock body) := by
      rw [cfg_context_blocks, finishBlocks, Array.getElem?_map, row]
      rfl
    have finalPresent : (cfgBlock body).insts[position]? = some (.eff (.replace owner value origin)) := by
      simpa only [cfgBlock, Array.getElem?_toList] using present
    obtain ⟨sourceOrigin, sameOrigin, _⟩ :=
      lowerContextAt_source_replacement_demand_sites accepted contextAt implAt finalRow finalPresent
    subst origin
    obtain ⟨upper, below, site, cursor⟩ :=
      canonical finalRow finalPresent
    obtain ⟨demand⟩ := replacementDemandContext_forContext accepted contextAt implAt
      site.source.site.source site.source.root_eq
    exact ⟨sourceOrigin, rfl, site.source.site,
      site_rhs_apart_of_canonical_cursor accepted contextAt implAt site demand below cursor⟩

theorem lowerContextAt_checkShrinkReplace_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {contextIndex : ContextId} {context : Context}
    (contextAt : module.contexts[contextIndex]? = some context) {impl : Core.Impl}
    (implAt : module.impls[context.impl]? = some impl) (label : String) :
    checkShrinkReplace (lower module) label (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module)) = .ok () :=
  lowerContextAt_checkShrinkReplace_of_canonical_occurrences accepted contextAt implAt
    (accepted_context_canonical_replacement_occurrences accepted contextAt implAt) label

private theorem lowerGlobal_checkShrinkReplace_of_rhs_occurrences {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {globalIndex : GlobalId} {global : Core.Global}
    (globalAt : module.globals[globalIndex]? = some global)
    (apart : ∀ {upper : Prov} {blockIndex position owner value : Nat} {origin : OriginId}
      (site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
        (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
        (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
        upper blockIndex position owner value origin),
      ReplacementDemandContext module (module.contexts.size + globalIndex)
        site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin →
      ProvenanceBelow ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) upper →
      EmitsOnly (ReplacementInstApart (lower module) ((lowerGlobal module global).init.valueTypes (lower module))
        (replacementQueries (lower module) (lowerGlobal module global).init
          ((lowerGlobal module global).init.valueTypes (lower module))) owner)
        site.source.site.source.site.cleared site.source.site.source.site.captured) (label : String) :
    checkShrinkReplace (lower module) label (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module)) = .ok () := by
  have builder := lowerGlobal_emittedBuilder_of_accepted accepted globalAt
  have graphs := lowerGlobal_mutableSnapshotGraphs_of_accepted accepted globalAt
  refine checkShrinkReplace_of_source_sites builder (cfg_global_blocks module global) rfl
    (lower_globalTypeTables module) (lower_signatureTables module) rfl rfl graphs
    (closedBlocks_of_finished (cfg_global_blocks module global) (lowerGlobal_terminators module global))
    (lowerGlobal_blocks_nonempty module global) ?_ ?_ label
  · intro index bounded
    exact lowerGlobal_emptyFacts_known module global _ _ bounded
  · intro index body row position owner value origin present
    have finalRow : (lowerGlobal module global).init.blocks[index]? = some (cfgBlock body) := by
      rw [cfg_global_blocks, finishBlocks, Array.getElem?_map, row]
      rfl
    have finalPresent : (cfgBlock body).insts[position]? = some (.eff (.replace owner value origin)) := by
      simpa only [cfgBlock, Array.getElem?_toList] using present
    obtain ⟨sourceOrigin, sameOrigin, _⟩ :=
      lowerGlobal_source_replacement_demand_sites accepted globalAt finalRow finalPresent
    subst origin
    obtain ⟨upper, below, site, ⟨demand⟩⟩ :=
      accepted_global_replacement_demand_occurrences accepted globalAt finalRow finalPresent
    exact ⟨sourceOrigin, rfl, site.source.site, apart site demand below⟩

theorem lowerGlobal_checkShrinkReplace_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {globalIndex : GlobalId} {global : Core.Global}
    (globalAt : module.globals[globalIndex]? = some global) (label : String) :
    checkShrinkReplace (lower module) label (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module)) = .ok () := by
  apply lowerGlobal_checkShrinkReplace_of_rhs_occurrences accepted globalAt
    (fun site demand below => site_global_rhs_apart_of_accepted accepted globalAt site demand below) label

private theorem lower_validate_of_context_replacements {module : Core.Module}
    (accepted : Core.validate module = .ok ())
    (contexts : ∀ (contextIndex : ContextId) (context : Context) (impl : Impl),
      module.contexts[contextIndex]? = some context → module.impls[context.impl]? = some impl →
      ∀ label, checkShrinkReplace (lower module) label (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module)) = .ok ()) :
    GIR.validate (lower module) = .ok () := by
  apply lower_validate_of_replacement_checks accepted
  apply Origins.checkAll_ok_of_forall
  intro info member
  obtain ⟨tables, source⟩ := lower_info_source accepted member
  rw [tables]
  rcases source with ⟨contextIndex, context, impl, contextAt, implAt, same⟩ |
    ⟨globalIndex, global, globalAt, same⟩
  · rw [same]
    exact contexts contextIndex context impl contextAt implAt info.label
  · rw [same]
    exact lowerGlobal_checkShrinkReplace_of_accepted accepted globalAt info.label

theorem lower_validate_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) : GIR.validate (lower module) = .ok () :=
  lower_validate_of_context_replacements accepted
    (fun _ _ _ contextAt implAt label =>
      lowerContextAt_checkShrinkReplace_of_accepted accepted contextAt implAt label)

#print axioms lowerContextAt_checkShrinkReplace_of_accepted
#print axioms lower_validate_of_accepted

#print axioms lowerContextAt_checkShrinkReplace_of_canonical_occurrences
#print axioms lowerGlobal_checkShrinkReplace_of_rhs_occurrences
#print axioms lowerGlobal_checkShrinkReplace_of_accepted
#print axioms lower_validate_of_context_replacements

end Goose.Lower.Validation
