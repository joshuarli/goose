import Goose.Lower.Validation.SourceReadyCanonicalInputs

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_context_module_ready_inputs {module : Core.Module} {context : Context} {impl : Impl}
    {index : ContextId} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {states : Array State} {state : State}
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states)
    (stateAt : states[index]? = some state) :
    ∃ facts : SourceReadyFunction,
      facts.source = ⟨module, impl, context, []⟩ ∧ facts.root = .block impl.body ∧
      facts.func = lowerContextAt module context impl ∧
      facts.types = (lowerContextAt module context impl).valueTypes (lower module) ∧
      facts.provenance = (lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount ∧
      facts.completed = cfg_implState module impl ∧
      facts.moduleTypes = (lower module).funcs.map (·.valueTypes (lower module)) ∧
      facts.resultRoots = resultRoots (lower module) (lower module).implTypes ∧
      facts.callees = states ∧ facts.state = state := by
  have native := lowerContext_canonical_facts_of_accepted accepted contextAt implAt
  have moduleFacts := lower_canonical_facts_of_accepted accepted
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  have moduleBounds := close_canonicalWithin moduleFacts annotations entries addresses closed
  have funcAt := lower_func_at contextAt implAt
  have typeAt : ((lower module).funcs.map (·.valueTypes (lower module)))[index]? =
      some ((lowerContextAt module context impl).valueTypes (lower module)) := by
    simp only [Array.getElem?_map, funcAt, Option.map_some]
  have initialAt : (moduleStart (lower module)
      ((lower module).funcs.map (·.valueTypes (lower module))))[index]? =
      some (start (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) := by
    simp only [moduleStart, Array.getElem?_mapIdx, funcAt, typeAt, Option.map_some, Option.getD_some]
  have growth := (close_initial_extends closed).values index
  simp only [initialAt, stateAt, Option.getD_some] at growth
  have fixed := moduleRound_fixed_function (close_fixed closed) index _ _ funcAt stateAt
  simp only [typeAt, Option.getD_some] at fixed
  obtain ⟨found, foundAt, canonical⟩ := moduleBounds.1.2 index _ funcAt
  have same : found = state := Option.some.inj (foundAt.symm.trans stateAt)
  subst found
  simp only [Array.getElem?_map, funcAt, Option.map_some, Option.getD_some] at canonical
  obtain ⟨upper, below, occurrences⟩ := accepted_context_instruction_occurrences accepted contextAt implAt
  let facts : SourceReadyFunction := {
    source := ⟨module, impl, context, []⟩
    root := .block impl.body
    func := lowerContextAt module context impl
    types := (lowerContextAt module context impl).valueTypes (lower module)
    provenance := (lowerContextAt module context impl).provenance
      (resultRoots (lower module) (lower module).implTypes)
      ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount
    upper := upper
    state := state
    completed := cfg_implState module impl
    moduleTypes := (lower module).funcs.map (·.valueTypes (lower module))
    moduleProvenances := (lower module).funcs.map fun func => func.provenance
      (resultRoots (lower module) (lower module).implTypes) (func.valueTypes (lower module)) (lower module).rootCount
    resultRoots := resultRoots (lower module) (lower module).implTypes
    callees := states
    accepted := accepted
    caller := .context index contextAt implAt
    closed := closed
    moduleFacts := moduleFacts
    moduleBounds := moduleBounds.1
    frame := ⟨fixed, canonical.shape, cfg_context_blocks module context impl,
      lowerContextAt_state_numValues module context impl⟩
    native := native
    canonical := canonical
    growth := growth
    occurrences := occurrences
    below := below.vals
    slotCount := by simp [lowerContextAt, lowerImpl, lowerImplFromState, lowerEnv]
    slotSeeds := fun _ _ row reference => lowerContext_canonical_refSlice_slot_seed_of_accepted
      accepted contextAt implAt row reference _ _ _ }
  exact ⟨facts, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms accepted_context_module_ready_inputs

end Goose.Lower.Validation.ReplacementContentFlowSource
