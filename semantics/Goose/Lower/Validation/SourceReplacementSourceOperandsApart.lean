import Goose.Lower.Validation.SourceReplacementScopedApart
import Goose.Lower.Validation.ReplacementConsumedReferenceBackingApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem site_consumed_reference_apart_of_calls {module : Core.Module}
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
    (calls : ∀ value block callee args callOrigin,
      block ∈ (lowerContextAt module context impl).blocks.toList →
      Inst.def value (.call callee args callOrigin) ∈ block.insts →
      ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
        (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
        upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value →
      ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner
        ((replacementQueries (lower module) (lowerContextAt module context impl)
          ((lowerContextAt module context impl).valueTypes (lower module))).ownerDependencies value))
    {value : ValueId} {consumerBlock : GIR.Block} {instruction : Inst}
    (consumerMember : consumerBlock ∈ (lowerContextAt module context impl).blocks.toList)
    (instructionMember : instruction ∈ consumerBlock.insts) (used : value ∈ instruction.uses)
    (lowerBound : site.source.site.source.site.cleared.vals.size ≤ value)
    (upperBound : value < site.source.site.source.site.captured.vals.size)
    {mutability : Mutability} {payload : Ty}
    (reference : ((lowerContextAt module context impl).valueTypes (lower module))[value]? =
      some (some (.data (.ref mutability payload))))
    (occurrence : ConsumedReferenceOccurrence site.localEnv (.expression site.source.site.source.rhs)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper value)
    :
    ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))) owner
      ((replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))).ownerDependencies value) := by
  have valueKnown := (lowerContext_operand_queries_within_provenance_of_accepted
    accepted contextAt implAt consumerMember instructionMember used).2.provenanceBelow below
  have bounded := (lowerContextAt_operand_bounds module context impl).1
    _ consumerMember _ instructionMember _ used
  obtain ⟨returned, rawKnown⟩ := accepted_context_factory_operand_value
    accepted contextAt implAt consumerMember instructionMember used
  obtain ⟨target, targetAt, ownerKnown⟩ :=
    site_owner_query_of_accepted accepted contextAt implAt site demand below
  have ownerQuery := ownerKnown
  obtain ⟨ownerRoots, ownerAt, _⟩ := ownerQuery
  have native : NativeRows ((lowerContextAt module context impl).valueTypes (lower module))
      (cfg_implState module impl) := by
    rw [lowerContext_valueTypes_of_accepted accepted implAt]
    exact NativeRows.refl _
  obtain ⟨ownerMutability, ownerType, ownerTypeAt, owning⟩ := site.source.site.source.owner_type native
  obtain ⟨replacementBlock, replacementMember, replacement⟩ :=
    site_replacement_instruction_member site (cfg_context_blocks module context impl)
  have ownerUsed : owner ∈ (Inst.eff (.replace owner replacementValue (some origin))).uses := by
    simp [Inst.uses, Effect.uses]
  have ownerBound := (lowerContextAt_operand_bounds module context impl).1
    _ replacementMember _ replacement _ ownerUsed
  have ownerRaw := ownerAt
  rw [replacementQueries_value _ _ _ _ ownerBound] at ownerRaw
  have facts := lowerContext_canonical_facts_of_accepted accepted contextAt implAt
  have dense := (dense_cfg_implAction impl (lowerEnv module impl.vars impl.results.toList) initState
    _ _ rfl LS.denseDefinitions_initState liveBound_initState).1
  have graph := site.source.site.source.scoped_graph_inputs (cfg_context_blocks module context impl)
    site.clearedOperandUses (lowerContextAt_operand_bounds module context impl).2 dense
  apply occurrence.apart_of_backings demand
    (site.access.trans (demand.access_context contextAt implAt).symm) targetAt
    (lowerContextAt_parameterRoots_closed accepted contextAt implAt) rfl
    (by simp [valRefLike, reference, VTy.refLike, Ty.isRefLike])
    (fun block member result op defined source used => facts.uses block member _ defined source used)
    ?_ ownerAt owning
    (fun slot present => lowerContext_factory_owner_local_of_accepted accepted contextAt implAt
      ownerTypeAt owning ownerRaw present) ownerKnown valueKnown rawKnown bounded
    ((lowerImpl_dense_definitions module impl).nodup_iff.mpr List.nodup_range)
  intro source op block member defined backing sourceType sourceAt carrier
  have sourceBounds := graph.2.1 block member value op defined lowerBound upperBound source backing.source_used
  have chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper
      site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size source :=
    ⟨sourceBounds.1, sourceBounds.2, Or.inl ⟨sourceType, sourceAt, carrier⟩⟩
  obtain ⟨sourceRoots, sourceKnown⟩ := accepted_context_factory_operand_value
    accepted contextAt implAt member defined backing.source_used
  have apart := site_scoped_origin_apart_of_leaves accepted contextAt implAt site
    (fun leafValue selected leaf => site_scoped_leaf_apart_of_calls accepted contextAt implAt site demand below
      calls selected leaf) chosen sourceKnown
  obtain ⟨dependencies, dependencyAt, _⟩ := ReplacementFunctionFlow.ownerDependencies_of_value sourceKnown
  have sourceBound := facts.uses block member _ defined source backing.source_used
  rw [replacementQueries_ownerDependencies _ _ _ _ sourceBound, dependencyAt] at apart
  exact ⟨dependencies, dependencyAt, apart⟩

theorem site_global_consumed_reference_apart_of_calls {module : Core.Module}
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
    (calls : ∀ value block callee args callOrigin,
      block ∈ (lowerGlobal module global).init.blocks.toList →
      Inst.def value (.call callee args callOrigin) ∈ block.insts →
      ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
        (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
        upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value →
      ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))) owner
        ((replacementQueries (lower module) (lowerGlobal module global).init
          ((lowerGlobal module global).init.valueTypes (lower module))).ownerDependencies value))
    {value : ValueId} {consumerBlock : GIR.Block} {instruction : Inst}
    (consumerMember : consumerBlock ∈ (lowerGlobal module global).init.blocks.toList)
    (instructionMember : instruction ∈ consumerBlock.insts) (used : value ∈ instruction.uses)
    (lowerBound : site.source.site.source.site.cleared.vals.size ≤ value)
    (upperBound : value < site.source.site.source.site.captured.vals.size)
    {mutability : Mutability} {payload : Ty}
    (reference : ((lowerGlobal module global).init.valueTypes (lower module))[value]? =
      some (some (.data (.ref mutability payload))))
    (occurrence : ConsumedReferenceOccurrence site.localEnv (.expression site.source.site.source.rhs)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper value)
    :
    ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))) owner
      ((replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))).ownerDependencies value) := by
  have valueKnown := (lowerGlobal_operand_queries_within_provenance_of_accepted
    accepted globalAt consumerMember instructionMember used).2.provenanceBelow below
  have bounded := (lowerGlobal_operand_bounds module global).1
    _ consumerMember _ instructionMember _ used
  obtain ⟨returned, rawKnown⟩ := accepted_global_factory_operand_value
    accepted globalAt consumerMember instructionMember used
  obtain ⟨target, targetAt, ownerKnown⟩ :=
    site_global_owner_query_of_accepted accepted globalAt site demand below
  have ownerQuery := ownerKnown
  obtain ⟨ownerRoots, ownerAt, _⟩ := ownerQuery
  have native : NativeRows ((lowerGlobal module global).init.valueTypes (lower module))
      (cfg_globalState module global) := by
    rw [lowerGlobal_valueTypes_of_accepted accepted globalAt]
    exact NativeRows.refl _
  obtain ⟨ownerMutability, ownerType, ownerTypeAt, owning⟩ := site.source.site.source.owner_type native
  obtain ⟨replacementBlock, replacementMember, replacement⟩ :=
    site_replacement_instruction_member site (cfg_global_blocks module global)
  have ownerUsed : owner ∈ (Inst.eff (.replace owner replacementValue (some origin))).uses := by
    simp [Inst.uses, Effect.uses]
  have ownerBound := (lowerGlobal_operand_bounds module global).1
    _ replacementMember _ replacement _ ownerUsed
  have ownerRaw := ownerAt
  rw [replacementQueries_value _ _ _ _ ownerBound] at ownerRaw
  have facts := lowerGlobal_canonical_facts_of_accepted accepted globalAt
  have dense := cfg_globalState_denseDefinitions module global
  have graph := site.source.site.source.scoped_graph_inputs (cfg_global_blocks module global)
    site.clearedOperandUses (lowerGlobal_operand_bounds module global).2 dense
  apply occurrence.apart_of_backings demand
    (site.access.trans demand.access_global.symm) targetAt
    (SummaryPreservation.global_initializer_parameterRoots_closed module global) rfl
    (by simp [valRefLike, reference, VTy.refLike, Ty.isRefLike])
    (fun block member result op defined source used => facts.uses block member _ defined source used)
    ?_ ownerAt owning
    (fun slot present => lowerGlobal_factory_owner_local_of_accepted accepted globalAt
      ownerTypeAt owning ownerRaw present) ownerKnown valueKnown rawKnown bounded
    ((lowerGlobal_dense_definitions module global).nodup_iff.mpr List.nodup_range)
  intro source op block member defined backing sourceType sourceAt carrier
  have sourceBounds := graph.2.1 block member value op defined lowerBound upperBound source backing.source_used
  have chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper
      site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size source :=
    ⟨sourceBounds.1, sourceBounds.2, Or.inl ⟨sourceType, sourceAt, carrier⟩⟩
  obtain ⟨sourceRoots, sourceKnown⟩ := accepted_global_factory_operand_value
    accepted globalAt member defined backing.source_used
  have apart := site_global_scoped_origin_apart_of_leaves accepted globalAt site
    (fun leafValue selected leaf => site_global_scoped_leaf_apart_of_calls accepted globalAt site demand below
      calls selected leaf) chosen sourceKnown
  obtain ⟨dependencies, dependencyAt, _⟩ := ReplacementFunctionFlow.ownerDependencies_of_value sourceKnown
  have sourceBound := facts.uses block member _ defined source backing.source_used
  rw [replacementQueries_ownerDependencies _ _ _ _ sourceBound, dependencyAt] at apart
  exact ⟨dependencies, dependencyAt, apart⟩

#print axioms site_global_consumed_reference_apart_of_calls
#print axioms site_consumed_reference_apart_of_calls

end Goose.Lower.Validation
