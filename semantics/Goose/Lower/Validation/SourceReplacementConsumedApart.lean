import Goose.Lower.Validation.SourceReplacementOwnerQueries
import Goose.Lower.Validation.ReplacementConsumedReferenceApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem ReplacementContentFlowSource.ScopedOrigin.reference_use
    {env : PEnv} {root : DemandNode} {func : Func} {types : Array (Option VTy)}
    {upper : Prov} {first last value : ValueId}
    (chosen : ScopedOrigin env root func types upper first last value)
    {mutability : Mutability} {payload : Ty}
    (reference : types[value]? = some (some (.data (.ref mutability payload)))) :
    ScopedReferenceUse func first last value := by
  rcases chosen.2.2 with ⟨type, typeAt, carrier⟩ | ⟨_, _, _, _, consumed⟩
  · have same : type = .data (.ref mutability payload) := by
      simpa only [Option.some.injEq] using typeAt.symm.trans reference
    subst type
    cases carrier
  · exact consumed

theorem site_unbacked_reference_apart_of_accepted {module : Core.Module}
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
    {value : ValueId}
    (chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value)
    {mutability : Mutability} {payload : Ty}
    (reference : ((lowerContextAt module context impl).valueTypes (lower module))[value]? =
      some (some (.data (.ref mutability payload))))
    (occurrence : ConsumedReferenceOccurrence site.localEnv (.expression site.source.site.source.rhs)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper value)
    (unbacked : ¬ ScopedTypedBacking (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module)) value) :
    ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))) owner
      ((replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))).ownerDependencies value) := by
  obtain ⟨consumer, op, block, member, defined, _, _, accessed⟩ := chosen.reference_use reference
  have used : value ∈ (Inst.def consumer op).uses := by
    cases op <;> simp only [accessOperands] at accessed <;> first | exact accessed | contradiction
  have valueKnown := (lowerContext_operand_queries_within_provenance_of_accepted
    accepted contextAt implAt member defined used).2.provenanceBelow below
  have bounded := (lowerContextAt_operand_bounds module context impl).1 _ member _ defined _ used
  obtain ⟨returned, rawKnown⟩ :=
    accepted_context_factory_operand_value accepted contextAt implAt member defined used
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
  exact occurrence.unbacked_apart demand unbacked
    (site.access.trans (demand.access_context contextAt implAt).symm) targetAt
    (lowerContextAt_parameterRoots_closed accepted contextAt implAt) ownerAt owning
    (fun slot present => lowerContext_factory_owner_local_of_accepted accepted contextAt implAt
      ownerTypeAt owning ownerRaw present) ownerKnown valueKnown rawKnown bounded
    ((lowerImpl_dense_definitions module impl).nodup_iff.mpr List.nodup_range)

theorem site_global_unbacked_reference_apart_of_accepted {module : Core.Module}
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
    {value : ValueId}
    (chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value)
    {mutability : Mutability} {payload : Ty}
    (reference : ((lowerGlobal module global).init.valueTypes (lower module))[value]? =
      some (some (.data (.ref mutability payload))))
    (occurrence : ConsumedReferenceOccurrence site.localEnv (.expression site.source.site.source.rhs)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper value)
    (unbacked : ¬ ScopedTypedBacking (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module)) value) :
    ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))) owner
      ((replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))).ownerDependencies value) := by
  obtain ⟨consumer, op, block, member, defined, _, _, accessed⟩ := chosen.reference_use reference
  have used : value ∈ (Inst.def consumer op).uses := by
    cases op <;> simp only [accessOperands] at accessed <;> first | exact accessed | contradiction
  have valueKnown := (lowerGlobal_operand_queries_within_provenance_of_accepted
    accepted globalAt member defined used).2.provenanceBelow below
  have bounded := (lowerGlobal_operand_bounds module global).1 _ member _ defined _ used
  obtain ⟨returned, rawKnown⟩ :=
    accepted_global_factory_operand_value accepted globalAt member defined used
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
  exact occurrence.unbacked_apart demand unbacked
    (site.access.trans demand.access_global.symm) targetAt
    (SummaryPreservation.global_initializer_parameterRoots_closed module global) ownerAt owning
    (fun slot present => lowerGlobal_factory_owner_local_of_accepted accepted globalAt
      ownerTypeAt owning ownerRaw present) ownerKnown valueKnown rawKnown bounded
    ((lowerGlobal_dense_definitions module global).nodup_iff.mpr List.nodup_range)

#print axioms site_global_unbacked_reference_apart_of_accepted
#print axioms ReplacementContentFlowSource.ScopedOrigin.reference_use
#print axioms site_unbacked_reference_apart_of_accepted

end Goose.Lower.Validation
