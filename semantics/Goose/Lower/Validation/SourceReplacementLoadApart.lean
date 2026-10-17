import Goose.Lower.Validation.SourceLoadQueryBounds
import Goose.Lower.Validation.SourceOccurrenceReplacementDemand
import Goose.Lower.Validation.ReplacementScopedLeafOccurrences
import Goose.Lower.Validation.ReplacementOccurrenceApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

theorem ReplacementRootsWithin.provenanceBelow {func : Func}
    {query : ReplacementRootQuery} {before after : Prov} {value : ValueId}
    (known : ReplacementRootsWithin query
      ((rootsAt before.vals value).flatMap func.expandParameterRoot))
    (below : ProvenanceBelow before after) :
    ReplacementRootsWithin query ((rootsAt after.vals value).flatMap func.expandParameterRoot) := by
  apply known.expanded_mono
  intro root member
  exact below.vals value root member

theorem site_replacement_instruction_member
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {block position owner value : Nat} {origin : OriginId}
    (site : SiteOccurrences env root targets le state func types upper
      block position owner value origin)
    (blocks : func.blocks = finishBlocks state.blocks) :
    ∃ finalBlock, finalBlock ∈ func.blocks.toList ∧
      Inst.eff (.replace owner value (some origin)) ∈ finalBlock.insts := by
  obtain ⟨index, capturedBody, finalBody, tail, _, _, finalRow, _, append⟩ :=
    site.source.site.source.occurrence
  let finalBlock := cfgBlock finalBody
  have row : func.blocks[index]? = some finalBlock := by
    rw [blocks, finishBlocks, Array.getElem?_map, finalRow]
    rfl
  refine ⟨finalBlock, Array.mem_toList_iff.mpr (Array.mem_of_getElem? row), ?_⟩
  change Inst.eff (.replace owner value (some origin)) ∈ finalBody.insts.toList
  rw [append]
  simp

theorem site_load_apart_of_accepted {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, impl, context, []⟩ (.block impl.body) []
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module contextIndex
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount)
      upper)
    {block : GIR.Block} (blockMember : block ∈ (lowerContextAt module context impl).blocks.toList)
    {loadedValue address : ValueId} (loaded : Inst.def loadedValue (.load address) ∈ block.insts)
    (occurrence : ReadOccurrence site.localEnv
      (.expression site.source.site.source.rhs) (lowerContextAt module context impl) upper loadedValue address) :
    ReplacementInstApart (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
      (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner (.def loadedValue (.load address)) := by
  have loadQueries := lowerContext_load_queries_within_provenance_of_accepted
    accepted contextAt implAt blockMember loaded rfl
  have addressKnown := loadQueries.1.provenanceBelow below
  have valueKnown := loadQueries.2.provenanceBelow below
  obtain ⟨replacementBlock, replacementBlockMember, replacementMember⟩ :=
    site_replacement_instruction_member site (cfg_context_blocks module context impl)
  have ownerUse : owner ∈ (Inst.eff (.replace owner replacementValue (some origin))).uses := by
    simp [Inst.uses, Effect.uses]
  have ownerQueries := lowerContext_operand_queries_within_provenance_of_accepted
    accepted contextAt implAt replacementBlockMember replacementMember (value := owner) ownerUse
  dsimp only at ownerQueries
  have ownerKnown := ownerQueries.1.provenanceBelow below
  have closed := lowerContextAt_parameterRoots_closed accepted contextAt implAt
  have ownerSourceKnown := ownerKnown.refined_expanded closed site.ownerRefined
  obtain ⟨target, targetAt, _⟩ := demand.owner_forbidden
  have access : site.localEnv.access = demand.planContext.approvals.access := by
    exact site.access.trans (demand.access_context contextAt implAt).symm
  have ownerTargetKnown := ownerSourceKnown.access_owner site.ownerReplay (access ▸ targetAt)
  exact ReplacementContentFlowSource.ReadOccurrence.apart demand occurrence access targetAt
    closed ownerTargetKnown addressKnown valueKnown

theorem site_fresh_load_apart_of_accepted {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, impl, context, []⟩ (.block impl.body) []
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module contextIndex
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount)
      upper)
    {block : GIR.Block} (blockMember : block ∈ (lowerContextAt module context impl).blocks.toList)
    {value address : ValueId} (loaded : Inst.def value (.load address) ∈ block.insts)
    (lowerBound : site.source.site.source.site.cleared.vals.size ≤ value)
    (upperBound : value < site.source.site.source.site.captured.vals.size)
    (reference : valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) value = true) :
    ReplacementInstApart (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
      (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner (.def value (.load address)) := by
  have origins := site.fresh_instruction_occurrences (cfg_context_blocks module context impl)
    (dense_cfg_implAction impl (lowerEnv module impl.vars impl.results.toList) initState
      _ _ rfl LS.denseDefinitions_initState liveBound_initState).1
    blockMember loaded lowerBound upperBound
  exact site_load_apart_of_accepted accepted contextAt implAt site demand below blockMember loaded
    (origins.2.1 value address rfl reference)

theorem site_global_load_apart_of_accepted {module : Core.Module}
    {globalIndex : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[globalIndex]? = some global)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module (module.contexts.size + globalIndex)
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount)
      upper)
    {block : GIR.Block} (blockMember : block ∈ (lowerGlobal module global).init.blocks.toList)
    {loadedValue address : ValueId} (loaded : Inst.def loadedValue (.load address) ∈ block.insts)
    (occurrence : ReadOccurrence site.localEnv
      (.expression site.source.site.source.rhs) (lowerGlobal module global).init upper loadedValue address) :
    ReplacementInstApart (lower module) ((lowerGlobal module global).init.valueTypes (lower module))
      (replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))) owner (.def loadedValue (.load address)) := by
  have loadQueries := lowerGlobal_load_queries_within_provenance_of_accepted
    accepted globalAt blockMember loaded rfl
  have addressKnown := loadQueries.1.provenanceBelow below
  have valueKnown := loadQueries.2.provenanceBelow below
  obtain ⟨replacementBlock, replacementBlockMember, replacementMember⟩ :=
    site_replacement_instruction_member site (cfg_global_blocks module global)
  have ownerUse : owner ∈ (Inst.eff (.replace owner replacementValue (some origin))).uses := by
    simp [Inst.uses, Effect.uses]
  have ownerQueries := lowerGlobal_operand_queries_within_provenance_of_accepted
    accepted globalAt replacementBlockMember replacementMember (value := owner) ownerUse
  dsimp only at ownerQueries
  have ownerKnown := ownerQueries.1.provenanceBelow below
  have closed := SummaryPreservation.global_initializer_parameterRoots_closed module global
  have ownerSourceKnown := ownerKnown.refined_expanded closed site.ownerRefined
  obtain ⟨target, targetAt, _⟩ := demand.owner_forbidden
  have access : site.localEnv.access = demand.planContext.approvals.access := by
    exact site.access.trans demand.access_global.symm
  have ownerTargetKnown := ownerSourceKnown.access_owner site.ownerReplay (access ▸ targetAt)
  exact ReplacementContentFlowSource.ReadOccurrence.apart demand occurrence access targetAt
    closed ownerTargetKnown addressKnown valueKnown

theorem site_fresh_global_load_apart_of_accepted {module : Core.Module}
    {globalIndex : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[globalIndex]? = some global)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module (module.contexts.size + globalIndex)
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount)
      upper)
    {block : GIR.Block} (blockMember : block ∈ (lowerGlobal module global).init.blocks.toList)
    {value address : ValueId} (loaded : Inst.def value (.load address) ∈ block.insts)
    (lowerBound : site.source.site.source.site.cleared.vals.size ≤ value)
    (upperBound : value < site.source.site.source.site.captured.vals.size)
    (reference : valRefLike ((lowerGlobal module global).init.valueTypes (lower module)) value = true) :
    ReplacementInstApart (lower module) ((lowerGlobal module global).init.valueTypes (lower module))
      (replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))) owner (.def value (.load address)) := by
  have origins := site.fresh_instruction_occurrences (cfg_global_blocks module global)
    (cfg_globalState_denseDefinitions module global) blockMember loaded lowerBound upperBound
  exact site_global_load_apart_of_accepted accepted globalAt site demand below blockMember loaded
    (origins.2.1 value address rfl reference)

end Goose.Lower.Validation
