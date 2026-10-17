import Goose.Lower.Validation.SourceReplacementCallContentsApartWrites
import Goose.Lower.Validation.SourceReplacementCallFootprintApart
import Goose.Lower.Validation.SourceReplacementContentMemoryApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem site_call_memory_apart_of_writer_localization {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {implementation : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implementationAt : module.impls[context.impl]? = some implementation)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, implementation, context, []⟩ (.block implementation.body) []
      (lowerEnv module implementation.vars implementation.results.toList) (cfg_implState module implementation)
      (lowerContextAt module context implementation)
      ((lowerContextAt module context implementation).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module contextIndex site.source.site.source.sourcePath
      site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context implementation).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context implementation).valueTypes (lower module)) (lower module).rootCount) upper)
    {states : Array State} {final current : State}
    (statesModel : (replacementContentFlow (lower module)).model = some states)
    (finalAt : ((replacementContentFlow (lower module)).forFunction
      (lowerContextAt module context implementation)
      ((lowerContextAt module context implementation).valueTypes (lower module))).model = some final)
    {block : GIR.Block} (member : block ∈ (lowerContextAt module context implementation).blocks.toList)
    {value function : Nat} {arguments : List ValueId} {callOrigin : Option OriginId}
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (growth : current.Extends final)
    (within : current.ScopedContentWithin
      (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
        (lowerContextAt module context implementation) ((lowerContextAt module context implementation).valueTypes (lower module))
        upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size)
      (RhsInactiveSliceHolder implementation site.source.site.source.rhs demand.statement.expected.frame.active)
      (fun _ => False)
      (OwnerDependencyApart (lower module) (lowerContextAt module context implementation)
        (replacementQueries (lower module) (lowerContextAt module context implementation)
          ((lowerContextAt module context implementation).valueTypes (lower module))) owner))
    (localized : ∀ (callee : Func), (lower module).funcs[function]? = some callee →
      ∀ (index argument : Nat), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      (callee.params[index]?).any Ty.isRefSlice = true → arguments[index]? = some argument →
      ∀ (slot : Nat), RhsInactiveSliceHolder implementation site.source.site.source.rhs demand.statement.expected.frame.active slot →
      RootRef.local slot ∈ rootsAt
        ((lowerContextAt module context implementation).provenance
          (resultRoots (lower module) (lower module).implTypes)
          ((lowerContextAt module context implementation).valueTypes (lower module)) (lower module).rootCount).vals argument →
      site.source.site.source.site.cleared.vals.size ≤ value ∧ value < site.source.site.source.site.captured.vals.size) :
    (callState (lower module) states (lowerContextAt module context implementation) current function arguments).2.ScopedMemoryWithin
      (RhsInactiveSliceHolder implementation site.source.site.source.rhs demand.statement.expected.frame.active)
      (fun _ => False)
      (OwnerDependencyApart (lower module) (lowerContextAt module context implementation)
        (replacementQueries (lower module) (lowerContextAt module context implementation)
          ((lowerContextAt module context implementation).valueTypes (lower module))) owner) := by
  have native := lowerContext_canonical_facts_of_accepted accepted contextAt implementationAt
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  have canonical := ReplacementContentFlow.forFunction_canonicalWithin native
    (lower_canonical_facts_of_accepted accepted) annotations entries addresses finalAt
  have moduleCanonical := close_canonicalWithin (lower_canonical_facts_of_accepted accepted)
    annotations entries addresses (replacementContentFlow_model_checked statesModel).2.1
  cases calleeAt : (lower module).funcs[function]? with
  | none =>
    simp only [callState, calleeAt, Id.run_pure]
    exact ⟨within.memory.slots, within.memory.contents⟩
  | some callee =>
    cases effectsAt : states[function]? with
    | none =>
      simp only [callState, calleeAt, effectsAt, Id.run_pure]
      exact ⟨within.memory.slots, within.memory.contents⟩
    | some effects =>
      obtain ⟨actual, actualAt, calleeCanonical⟩ := moduleCanonical.1.2 function callee calleeAt
      have effectsEq : actual = effects := Option.some.inj (actualAt.symm.trans effectsAt)
      subst actual
      apply within.memory.callState calleeAt effectsAt
      intro type index parameterPair reference raw writeAt
      have formal : callee.params[index]? = some type := List.mem_zipIdx_iff_getElem?.mp parameterPair
      have observed := calleeCanonical.writeRows index
        (by rw [calleeCanonical.shape.writes]; exact (List.getElem?_eq_some_iff.mp formal).1) raw writeAt
      have typeReference : (callee.params[index]?).any Ty.isRefSlice = true := by simp [formal, reference]
      obtain ⟨outer, inner, element, typeEq, flat⟩ := isRefSlice_shape reference
      subst type
      obtain ⟨callFacts⟩ := native.calls block member value function arguments callOrigin called
      have calleeEq : callFacts.callee = callee := Option.some.inj (callFacts.calleeAt.symm.trans calleeAt)
      obtain ⟨argument, actualMu, argumentAt, typed, bounded⟩ := callFacts.references index outer (.slice inner element)
        (by simpa only [calleeEq] using formal)
      have physical := (growth.values.values argument).atomsWithin
        (canonical.holderValues argument (by rw [canonical.shape.values]; exact bounded) actualMu
          (.slice inner element) typed rfl)
      change HolderRoots _ _ _ (flowAt current.values argument) at physical
      simp only [argumentAt, Option.map_some, Option.getD_some]
      refine ⟨?_, ?_⟩
      · intro unknown
        rw [unknown] at physical
        exact physical
      · intro actual addressAt
        refine ⟨?_, ?_⟩
        · intro slot selected atomAt
          have holder := physical
          rw [addressAt] at holder
          obtain ⟨storage, row, type, rootAt⟩ := (holder (.local slot) atomAt).local
          have fresh := localized callee calleeAt index argument observed typeReference argumentAt slot selected rootAt
          have dense := (dense_cfg_implAction implementation (lowerEnv module implementation.vars implementation.results.toList)
            initState _ _ rfl LS.denseDefinitions_initState liveBound_initState).1
          have occurrence := (site.fresh_instruction_occurrences (cfg_context_blocks module context implementation)
            dense member called fresh.1 fresh.2).2.2.1 value function arguments callOrigin rfl
          apply site_call_assigned_apart_of_contents accepted contextAt implementationAt site demand below member called fresh
            calleeAt occurrence statesModel effectsAt finalAt growth within.values
            (List.getElem?_eq_some_iff.mp formal).1 writeAt
          intro observedIndex observed reference argument argumentAt
          exact site_native_call_contents_apart_of_scoped_memory accepted contextAt implementationAt site demand below
            finalAt member called calleeAt observed occurrence argumentAt growth within.memory
        · intro index impossible
          exact False.elim impossible

#print axioms site_call_memory_apart_of_writer_localization

end Goose.Lower.Validation
