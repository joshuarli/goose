import Goose.Lower.Validation.SourceReplacementScopedContentApart
import Goose.Lower.Validation.SourceReplacementContentMemoryApart
import Goose.Lower.Validation.SourceReplacementCallContentsApartCalls

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem site_scoped_content_atoms_of_memory_transfers {module : Core.Module}
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
    {final : State}
    (calls : ∀ states, (replacementContentFlow (lower module)).model = some states →
      ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ value function arguments origin,
      Inst.def value (.call function arguments origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) →
        current.Extends final →
        ((callState (lower module) states (lowerContextAt module context impl) current function arguments).2).ScopedMemoryWithin (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False)
          (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (initializations : ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ slot value origin, Inst.eff (.slotInit slot value origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) →
        current.Extends final → RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active slot → (flowAt current.values value).AtomsWithin
          (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (stores : ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ address value origin, Inst.eff (.store address value origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) →
        current.Extends final → valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) value = true →
        (write (lowerContextAt module context impl) (touchValues ((lowerContextAt module context impl).valueTypes (lower module)) current [address]) (flowAt current.values address)
          (flowAt current.values value)).ScopedMemoryWithin (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (finalAt : ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final) :
    final.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) := by
  apply site_scoped_content_atoms_of_accepted_leaves accepted contextAt implAt site demand below
    (slots := RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active)
    (contents := fun _ => False) ?_ ?_ initializations stores finalAt
  · apply start_scoped_memory
    · intro slot selected
      obtain ⟨localVar, row, slice, used, inactive⟩ := selected
      simpa only [lowerContextAt, lowerImpl, lowerImplFromState, lowerEnv, Array.size_map, Array.size_mapIdx] using
        (Array.getElem?_eq_some_iff.mp row).1
    · intro index impossible
      contradiction
  · intro states statesModel actual actualAt block member value function arguments callOrigin called
      current within growth
    constructor
    · intro chosen notLeaf
      have dense := (dense_cfg_implAction impl (lowerEnv module impl.vars impl.results.toList) initState
        _ _ rfl LS.denseDefinitions_initState liveBound_initState).1
      have occurrence := (site.fresh_instruction_occurrences (cfg_context_blocks module context impl) dense
        member called chosen.1 chosen.2.1).2.2.1 value function arguments callOrigin rfl
      apply site_call_returned_apart_of_contents accepted contextAt implAt site demand below member called occurrence
        statesModel actualAt chosen notLeaf growth within.values
      intro callee calleeAt index observed reference argument argumentAt
      exact site_native_call_contents_apart_of_scoped_memory accepted contextAt implAt site demand below actualAt
        member called calleeAt observed occurrence argumentAt growth within.memory
    · exact calls states statesModel actual actualAt block member value function arguments callOrigin called
        current within growth

theorem site_rhs_apart_of_memory_transfers {module : Core.Module}
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
    (calls : ∀ states, (replacementContentFlow (lower module)).model = some states →
      ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ value function arguments origin,
      Inst.def value (.call function arguments origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) →
        current.Extends final →
        ((callState (lower module) states (lowerContextAt module context impl) current function arguments).2).ScopedMemoryWithin (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False)
          (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (initializations : ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ slot value origin, Inst.eff (.slotInit slot value origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) →
        current.Extends final → RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active slot → (flowAt current.values value).AtomsWithin
          (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (stores : ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ address value origin, Inst.eff (.store address value origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) →
        current.Extends final → valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) value = true →
        (write (lowerContextAt module context impl) (touchValues ((lowerContextAt module context impl).valueTypes (lower module)) current [address]) (flowAt current.values address)
          (flowAt current.values value)).ScopedMemoryWithin (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
 :
    EmitsOnly (ReplacementInstApart (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
      (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  obtain ⟨facts, sourceEq, functionEq, typesEq, completedEq, model, ready, observed⟩ :=
    accepted_context_factory_ready_inputs accepted contextAt implAt
  have finalAt : ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).model = some facts.state := by
    simpa only [functionEq, typesEq] using model
  have within := site_scoped_content_atoms_of_memory_transfers accepted contextAt implAt site demand below
    calls initializations stores finalAt
  exact site_rhs_apart_of_final_scoped_memory accepted contextAt implAt site demand below finalAt within

theorem site_rhs_apart_of_writer_intervals {module : Core.Module}
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
    (calls : ∀ states, (replacementContentFlow (lower module)).model = some states →
      ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ value function arguments origin,
      Inst.def value (.call function arguments origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) →
        current.Extends final →
        ((callState (lower module) states (lowerContextAt module context impl) current function arguments).2).ScopedMemoryWithin (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active) (fun _ => False)
          (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (initialBounds : ∀ block ∈ (lowerContextAt module context impl).blocks.toList,
      ∀ slot value origin, Inst.eff (.slotInit slot value origin) ∈ block.insts →
      RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active slot →
      site.source.site.source.site.cleared.vals.size ≤ value ∧ value < site.source.site.source.site.captured.vals.size)
    (storeBounds : ∀ block ∈ (lowerContextAt module context impl).blocks.toList,
      ∀ address value origin, Inst.eff (.store address value origin) ∈ block.insts →
      valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) value = true →
      ∀ slot, RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active slot →
      RootRef.local slot ∈ rootsAt ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount).vals address →
      site.source.site.source.site.cleared.vals.size ≤ value ∧ value < site.source.site.source.site.captured.vals.size) :
    EmitsOnly (ReplacementInstApart (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
      (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  have native := lowerContext_canonical_facts_of_accepted accepted contextAt implAt
  have slotsTyped : ∀ slot, RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active slot →
      ∃ storage, (lowerContextAt module context impl).slots[slot]? = some storage ∧ storage.ty.isSlice = true := by
    intro slot chosen
    exact rhs_inactive_slice_holder_native chosen
  apply site_rhs_apart_of_memory_transfers accepted contextAt implAt site demand below calls
  · intro final finalAt block member slot value sourceOrigin present current within growth chosen
    apply within.values value
    apply scoped_slotInit_source (native.typing block member _ present) slotsTyped chosen
    intro type typed slice
    exact slice_source_scoped_origin typed slice (initialBounds block member slot value sourceOrigin present chosen)
  · intro final finalAt block member address value sourceOrigin present current within growth reference
    obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
    have canonical := ReplacementContentFlow.forFunction_canonicalWithin native
      (lower_canonical_facts_of_accepted accepted) annotations entries addresses finalAt
    apply canonical_scoped_store_memory canonical growth (native.typing block member _ present)
      ((lowerContextAt_operand_bounds module context impl).1 block member _ present address (by simp [Inst.uses, Effect.uses]))
      reference within slotsTyped
    intro slot type chosen included typed slice
    exact slice_source_scoped_origin typed slice
      (storeBounds block member address value sourceOrigin present reference slot chosen included)

theorem site_rhs_apart_of_localized_writers {module : Core.Module}
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
    (callBounds : ∀ block ∈ (lowerContextAt module context impl).blocks.toList,
      ∀ value function arguments callOrigin, Inst.def value (.call function arguments callOrigin) ∈ block.insts →
      ∀ (callee : Func), (lower module).funcs[function]? = some callee →
      ∀ (index argument : Nat), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      (callee.params[index]?).any Ty.isRefSlice = true → arguments[index]? = some argument →
      ∀ slot, RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active slot →
      RootRef.local slot ∈ rootsAt ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount).vals argument →
      site.source.site.source.site.cleared.vals.size ≤ value ∧ value < site.source.site.source.site.captured.vals.size)
    (initialBounds : ∀ block ∈ (lowerContextAt module context impl).blocks.toList,
      ∀ slot value origin, Inst.eff (.slotInit slot value origin) ∈ block.insts →
      RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active slot →
      site.source.site.source.site.cleared.vals.size ≤ value ∧ value < site.source.site.source.site.captured.vals.size)
    (storeBounds : ∀ block ∈ (lowerContextAt module context impl).blocks.toList,
      ∀ address value origin, Inst.eff (.store address value origin) ∈ block.insts →
      valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) value = true →
      ∀ slot, RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active slot →
      RootRef.local slot ∈ rootsAt ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount).vals address →
      site.source.site.source.site.cleared.vals.size ≤ value ∧ value < site.source.site.source.site.captured.vals.size) :
    EmitsOnly (ReplacementInstApart (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
      (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  apply site_rhs_apart_of_writer_intervals accepted contextAt implAt site demand below ?_ initialBounds storeBounds
  intro states statesModel final finalAt block member value function arguments callOrigin called current within growth
  exact site_call_memory_apart_of_writer_localization accepted contextAt implAt site demand below statesModel finalAt
    member called growth within (callBounds block member value function arguments callOrigin called)

#print axioms site_rhs_apart_of_localized_writers

#print axioms site_rhs_apart_of_writer_intervals

#print axioms site_rhs_apart_of_memory_transfers

#print axioms site_scoped_content_atoms_of_memory_transfers

end Goose.Lower.Validation
