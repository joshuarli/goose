import Goose.Lower.Validation.ReplacementSourceCheck
import Goose.Lower.Validation.ReplacementDemandSites
import Goose.Lower.Validation.CfgFunctionCompletion
import Goose.Lower.Validation.FunctionTables

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ReplacementDemandSourceApart (source : Core.Module) (planOwner : Nat) (root : DemandNode)
    (le : LEnv) (state : LS) (module : GIR.Module) (func : Func) : Prop :=
  ∀ {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite le state owner value origin),
    site.sourceRoot = root →
    ReplacementDemandContext source planOwner site.sourcePath site.place site.rhs origin →
    EmitsOnly (ReplacementInstApart module (func.valueTypes module)
      (replacementQueries module func (func.valueTypes module)) owner)
      site.site.cleared site.site.captured

theorem closedBlocks_of_finished {state : LS} {func : Func}
    (blocks : func.blocks = finishBlocks state.blocks)
    (finished : ∀ block ∈ func.blocks.toList, block.terms.length = 1 ∧ block.lastTerm?.isSome = true) :
    ∀ body ∈ state.blocks.toList, ClosedBlock body := by
  intro body member
  apply finished (cfgBlock body)
  rw [blocks]
  simp only [finishBlocks, Array.toList_map]
  exact List.mem_map.mpr ⟨body, member, rfl⟩

theorem lowerContextAt_checkShrinkReplace_of_source_apart {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {contextIndex : ContextId} {context : Context}
    (contextAt : module.contexts[contextIndex]? = some context) {impl : Core.Impl}
    (implAt : module.impls[context.impl]? = some impl)
    (builder : EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState (cfg_implState module impl))
    (graphs : MutableSnapshotGraphs (lower module) (lowerContextAt module context impl) (cfg_implState module impl))
    (apart : ReplacementDemandSourceApart module contextIndex (.block impl.body)
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lower module) (lowerContextAt module context impl)) (label : String) :
    checkShrinkReplace (lower module) label (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module)) = .ok () := by
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
    obtain ⟨sourceOrigin, sameOrigin, site, rootEq, ⟨demand⟩⟩ :=
      lowerContextAt_source_replacement_demand_sites accepted contextAt implAt finalRow finalPresent
    exact ⟨sourceOrigin, sameOrigin, site, apart site.source rootEq demand⟩

theorem lowerGlobal_checkShrinkReplace_of_source_apart {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {globalIndex : GlobalId} {global : Core.Global}
    (globalAt : module.globals[globalIndex]? = some global)
    (builder : EmittedBuilder (lowerEnv module #[] [global.ty]) initState (cfg_globalState module global))
    (graphs : MutableSnapshotGraphs (lower module) (lowerGlobal module global).init (cfg_globalState module global))
    (apart : ReplacementDemandSourceApart module (module.contexts.size + globalIndex) (.expression global.init)
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lower module) (lowerGlobal module global).init) (label : String) :
    checkShrinkReplace (lower module) label (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module)) = .ok () := by
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
    obtain ⟨sourceOrigin, sameOrigin, site, rootEq, ⟨demand⟩⟩ :=
      lowerGlobal_source_replacement_demand_sites accepted globalAt finalRow finalPresent
    exact ⟨sourceOrigin, sameOrigin, site, apart site.source rootEq demand⟩

#print axioms lowerContextAt_checkShrinkReplace_of_source_apart
#print axioms lowerGlobal_checkShrinkReplace_of_source_apart

end Goose.Lower.Validation
