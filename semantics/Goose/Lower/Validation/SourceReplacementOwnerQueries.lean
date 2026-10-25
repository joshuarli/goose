import Goose.Lower.Validation.SourceReplacementLoadApart
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

theorem AcceptedReplacementSite.owner_type {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite le state owner value origin)
    {types : Array (Option VTy)} (native : NativeRows types state) :
    ∃ mutability payload, types[owner]? = some (some (.data (.ref mutability payload))) ∧
      payload.ownerElem?.isSome = true := by
  obtain ⟨info, element, childStart, source, shape, _, _, _, _⟩ :=
    tyStmt_assignWhole_children site.accepted
  have run : lowerPlace site.place
      (lowerEnv site.sourceEnv.mod site.sourceEnv.vars site.results)
      site.initial = (site.site.owner, site.site.addressed) := by
    simpa only [site.environment] using site.site.addressRun
  have clearedLive := (dead_lowerExpr site.rhs).live_before site.site.rhsRun site.live
  have addressedLive := (dead_emitEffect (.clear site.site.owner (some origin))).live_before
    site.site.clearRun clearedLive
  obtain ⟨mutability, row⟩ := lowerPlace_generated_typed site.place source run addressedLive site.generated
  have finalRow := native _ _ (site.types _ _ row)
  refine ⟨mutability, info.ty, site.owner_eq ▸ finalRow, ?_⟩
  rcases shape with grow | shrink
  · simp [grow, Ty.ownerElem?]
  · simp [shrink, Ty.ownerElem?]

theorem site_owner_query_of_accepted {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {upper : Prov} {blockIndex position owner value : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, impl, context, []⟩ (.block impl.body) []
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper blockIndex position owner value origin)
    (demand : ReplacementDemandContext module contextIndex
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount)
      upper) :
    ∃ target, demand.planContext.approvals.access.owner site.source.site.source.place = .ok target ∧
      ReplacementRootsWithin
        ((replacementQueries (lower module) (lowerContextAt module context impl)
          ((lowerContextAt module context impl).valueTypes (lower module))).value owner)
        (target.roots.flatMap (lowerContextAt module context impl).expandParameterRoot) := by
  obtain ⟨block, member, replacement⟩ :=
    site_replacement_instruction_member site (cfg_context_blocks module context impl)
  have used : owner ∈ (Inst.eff (.replace owner value (some origin))).uses := by
    simp [Inst.uses, Effect.uses]
  have known := (lowerContext_operand_queries_within_provenance_of_accepted
    accepted contextAt implAt member replacement used).1
  have sourceKnown := (known.provenanceBelow below).refined_expanded
    (lowerContextAt_parameterRoots_closed accepted contextAt implAt) site.ownerRefined
  obtain ⟨target, targetAt, _⟩ := demand.owner_forbidden
  have access : site.localEnv.access = demand.planContext.approvals.access :=
    site.access.trans (demand.access_context contextAt implAt).symm
  exact ⟨target, targetAt, sourceKnown.access_owner site.ownerReplay (access ▸ targetAt)⟩

theorem site_global_owner_query_of_accepted {module : Core.Module}
    {globalIndex : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[globalIndex]? = some global)
    {upper : Prov} {blockIndex position owner value : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper blockIndex position owner value origin)
    (demand : ReplacementDemandContext module (module.contexts.size + globalIndex)
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount)
      upper) :
    ∃ target, demand.planContext.approvals.access.owner site.source.site.source.place = .ok target ∧
      ReplacementRootsWithin
        ((replacementQueries (lower module) (lowerGlobal module global).init
          ((lowerGlobal module global).init.valueTypes (lower module))).value owner)
        (target.roots.flatMap (lowerGlobal module global).init.expandParameterRoot) := by
  obtain ⟨block, member, replacement⟩ :=
    site_replacement_instruction_member site (cfg_global_blocks module global)
  have used : owner ∈ (Inst.eff (.replace owner value (some origin))).uses := by
    simp [Inst.uses, Effect.uses]
  have known := (lowerGlobal_operand_queries_within_provenance_of_accepted
    accepted globalAt member replacement used).1
  have sourceKnown := (known.provenanceBelow below).refined_expanded
    (SummaryPreservation.global_initializer_parameterRoots_closed module global) site.ownerRefined
  obtain ⟨target, targetAt, _⟩ := demand.owner_forbidden
  have access : site.localEnv.access = demand.planContext.approvals.access :=
    site.access.trans demand.access_global.symm
  exact ⟨target, targetAt, sourceKnown.access_owner site.ownerReplay (access ▸ targetAt)⟩

#print axioms AcceptedReplacementSite.owner_type
#print axioms site_owner_query_of_accepted
#print axioms site_global_owner_query_of_accepted

end Goose.Lower.Validation
