import Goose.Lower.Validation.SourceCallSliceDependencies
import Goose.Lower.Validation.SourceReplacementRhsApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem ReplacementApart.of_call_result {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner callee : ValueId} {arguments : List ValueId}
    {query : ReplacementRootQuery} {dependencies roots : List RootRef}
    (apart : ReplacementApart queries owner (callDependencies module types queries callee arguments))
    (resultAt : query = some dependencies) (callAt : queries.callRoots callee arguments = some roots)
    (included : dependencies ⊆ roots) : ReplacementApart queries owner query := by
  have fromKnown : ∀ upper, callDependencies module types queries callee arguments = some upper →
      ReplacementApart queries owner query := by
    intro upper known
    obtain ⟨actual, actualAt, within⟩ := callDependencies_callRoots_subset known
    have same : actual = roots := Option.some.inj (actualAt.symm.trans callAt)
    subst actual
    rw [resultAt]
    exact apart.of_subset known (included.trans within)
  rcases apart with empty | empty | ⟨upper, _, known, _, _⟩
  · exact fromKnown [] empty
  · exact Or.inr (Or.inl empty)
  · exact fromKnown upper known

theorem site_scoped_call_result_apart_of_call_apart {module : Core.Module}
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
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount) upper)
    {value : ValueId}
    (chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value)
    {block : GIR.Block} {callee : FnId} {args : List ValueId} {callOrigin : Option OriginId}
    (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    (called : Inst.def value (.call callee args callOrigin) ∈ block.insts)
    (apart : ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))) owner
      (callDependencies (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
        (replacementQueries (lower module) (lowerContextAt module context impl)
          ((lowerContextAt module context impl).valueTypes (lower module))) callee args)) :
    ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))) owner
      ((replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))).ownerDependencies value) := by
  rcases chosen.2.2 with ⟨type, typeAt, carrier⟩ | ⟨mutability, payload, typeAt, occurrence, _⟩
  · cases carrier with
    | slice mutability element =>
      obtain ⟨dependencies, roots, dependencyAt, callAt, included⟩ :=
        lowerContext_call_slice_dependencies_of_accepted accepted contextAt implAt member called typeAt
      exact apart.of_call_result dependencyAt callAt included
    | view mutability element =>
      have facts := lowerContext_canonical_facts_of_accepted accepted contextAt implAt
      obtain ⟨site⟩ := facts.calls block member value callee args callOrigin called
      rcases facts.callResults block member value callee args callOrigin called site.callee site.calleeAt with
        ⟨_, unit⟩ | ⟨_, _, canonical⟩
      · rw [unit] at typeAt
        cases typeAt
      · rw [canonical] at typeAt
        cases typeAt
  · have unique : ((lowerContextAt module context impl).blocks.toList.flatMap GIR.Block.defs).Nodup :=
      (lowerImpl_dense_definitions module impl).nodup_iff.mpr List.nodup_range
    have unbacked : ¬ ScopedTypedBacking (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module)) value := by
      intro ⟨source, op, other, otherMember, defined, backing, _, _, _⟩
      have same := unique_definition_op unique member called otherMember defined
      subst op
      exact backing.noncall callee args callOrigin rfl
    exact site_unbacked_reference_apart_of_accepted accepted contextAt implAt site demand below
      chosen typeAt occurrence unbacked

theorem site_global_scoped_call_result_apart_of_call_apart {module : Core.Module}
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
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) upper)
    {value : ValueId}
    (chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value)
    {block : GIR.Block} {callee : FnId} {args : List ValueId} {callOrigin : Option OriginId}
    (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    (called : Inst.def value (.call callee args callOrigin) ∈ block.insts)
    (apart : ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))) owner
      (callDependencies (lower module) ((lowerGlobal module global).init.valueTypes (lower module))
        (replacementQueries (lower module) (lowerGlobal module global).init
          ((lowerGlobal module global).init.valueTypes (lower module))) callee args)) :
    ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))) owner
      ((replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))).ownerDependencies value) := by
  rcases chosen.2.2 with ⟨type, typeAt, carrier⟩ | ⟨mutability, payload, typeAt, occurrence, _⟩
  · cases carrier with
    | slice mutability element =>
      obtain ⟨dependencies, roots, dependencyAt, callAt, included⟩ :=
        lowerGlobal_call_slice_dependencies_of_accepted accepted globalAt member called typeAt
      exact apart.of_call_result dependencyAt callAt included
    | view mutability element =>
      have facts := lowerGlobal_canonical_facts_of_accepted accepted globalAt
      obtain ⟨site⟩ := facts.calls block member value callee args callOrigin called
      rcases facts.callResults block member value callee args callOrigin called site.callee site.calleeAt with
        ⟨_, unit⟩ | ⟨_, _, canonical⟩
      · rw [unit] at typeAt
        cases typeAt
      · rw [canonical] at typeAt
        cases typeAt
  · have unique : ((lowerGlobal module global).init.blocks.toList.flatMap GIR.Block.defs).Nodup :=
      (lowerGlobal_dense_definitions module global).nodup_iff.mpr List.nodup_range
    have unbacked : ¬ ScopedTypedBacking (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module)) value := by
      intro ⟨source, op, other, otherMember, defined, backing, _, _, _⟩
      have same := unique_definition_op unique member called otherMember defined
      subst op
      exact backing.noncall callee args callOrigin rfl
    exact site_global_unbacked_reference_apart_of_accepted accepted globalAt site demand below
      chosen typeAt occurrence unbacked

#print axioms site_global_scoped_call_result_apart_of_call_apart
theorem site_rhs_apart_of_call_effects {module : Core.Module}
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
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount) upper)
    (callEffects : ∀ value block callee args callOrigin,
      block ∈ (lowerContextAt module context impl).blocks.toList →
      Inst.def value (.call callee args callOrigin) ∈ block.insts →
      CallOccurrence site.localEnv (.expression site.source.site.source.rhs)
        (lowerContextAt module context impl) upper value callee args callOrigin →
      ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner
        (callDependencies (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
          (replacementQueries (lower module) (lowerContextAt module context impl)
            ((lowerContextAt module context impl).valueTypes (lower module))) callee args)) :
    EmitsOnly (ReplacementInstApart (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
      (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  apply site_rhs_apart_of_calls accepted contextAt implAt site demand below ?_ callEffects
  intro value block callee args callOrigin member called chosen
  have dense := (dense_cfg_implAction impl (lowerEnv module impl.vars impl.results.toList) initState
    _ _ rfl LS.denseDefinitions_initState liveBound_initState).1
  have occurrence := (site.fresh_instruction_occurrences (cfg_context_blocks module context impl) dense
    member called chosen.1 chosen.2.1).2.2.1 value callee args callOrigin rfl
  exact site_scoped_call_result_apart_of_call_apart accepted contextAt implAt site demand below chosen member called
    (callEffects value block callee args callOrigin member called occurrence)

#print axioms site_rhs_apart_of_call_effects
theorem site_global_rhs_apart_of_call_effects {module : Core.Module}
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
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) upper)
    (callEffects : ∀ value block callee args callOrigin,
      block ∈ (lowerGlobal module global).init.blocks.toList →
      Inst.def value (.call callee args callOrigin) ∈ block.insts →
      CallOccurrence site.localEnv (.expression site.source.site.source.rhs)
        (lowerGlobal module global).init upper value callee args callOrigin →
      ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))) owner
        (callDependencies (lower module) ((lowerGlobal module global).init.valueTypes (lower module))
          (replacementQueries (lower module) (lowerGlobal module global).init
            ((lowerGlobal module global).init.valueTypes (lower module))) callee args)) :
    EmitsOnly (ReplacementInstApart (lower module) ((lowerGlobal module global).init.valueTypes (lower module))
      (replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  apply site_global_rhs_apart_of_calls accepted globalAt site demand below ?_ callEffects
  intro value block callee args callOrigin member called chosen
  have dense := cfg_globalState_denseDefinitions module global
  have occurrence := (site.fresh_instruction_occurrences (cfg_global_blocks module global) dense
    member called chosen.1 chosen.2.1).2.2.1 value callee args callOrigin rfl
  exact site_global_scoped_call_result_apart_of_call_apart accepted globalAt site demand below chosen member called
    (callEffects value block callee args callOrigin member called occurrence)

#print axioms site_global_rhs_apart_of_call_effects
#print axioms ReplacementApart.of_call_result
#print axioms site_scoped_call_result_apart_of_call_apart

end Goose.Lower.Validation
