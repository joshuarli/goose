import Goose.Lower.Validation.SourceReadyInductionFacts
import Goose.Lower.Validation.SourceCanonicalFactsAssembly
import Goose.Lower.Validation.SourceCanonicalFactsSlotSeeds
import Goose.Lower.Validation.SourceOccurrenceInstructions
import Goose.Lower.Validation.ReplacementContentFlowSourceClosure

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_context_ready_inputs {module : Core.Module} {context : Context} {impl : Impl}
    {index : ContextId} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
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
      FunctionReachable (lower module) facts.callees facts.func facts.types
        (start facts.func facts.types) facts.state ∧
      closeFunction (lower module) facts.callees facts.func facts.types =
        if check (lower module) facts.func facts.types facts.state then some facts.state else none := by
  obtain ⟨callees, closed, finite, stable⟩ := accepted_module_close_finite accepted
  have native := lowerContext_canonical_facts_of_accepted accepted contextAt implAt
  have moduleFacts := lower_canonical_facts_of_accepted accepted
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  have moduleBounds := close_canonicalWithin moduleFacts annotations entries addresses closed
  obtain ⟨state, reachable, stateFinite, fixed, outcome⟩ :=
    accepted_function_solver_outcome accepted (lower_func_at contextAt implAt) closed
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
    callees := callees
    accepted := accepted
    caller := .context index contextAt implAt
    closed := closed
    moduleFacts := moduleFacts
    moduleBounds := moduleBounds.1
    frame := ⟨fixed, stateFinite.2, cfg_context_blocks module context impl,
      lowerContextAt_state_numValues module context impl⟩
    native := native
    canonical := reachable.canonicalWithin native.start native moduleFacts moduleBounds.1 finite.1
    growth := reachable.extends
    occurrences := occurrences
    below := below.vals
    slotCount := by simp [lowerContextAt, lowerImpl, lowerImplFromState, lowerEnv]
    slotSeeds := fun _ _ row reference => lowerContext_canonical_refSlice_slot_seed_of_accepted
      accepted contextAt implAt row reference _ _ _ }
  exact ⟨facts, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, reachable, outcome⟩

theorem accepted_global_ready_inputs {module : Core.Module} {global : Core.Global}
    {index : GlobalId} (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global) :
    ∃ facts : SourceReadyFunction,
      facts.source = ⟨module, Core.initImpl, Core.initContext, []⟩ ∧ facts.root = .expression global.init ∧
      facts.func = (lowerGlobal module global).init ∧
      facts.types = (lowerGlobal module global).init.valueTypes (lower module) ∧
      facts.provenance = (lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount ∧
      facts.completed = cfg_globalState module global ∧
      facts.moduleTypes = (lower module).funcs.map (·.valueTypes (lower module)) ∧
      facts.resultRoots = resultRoots (lower module) (lower module).implTypes ∧
      FunctionReachable (lower module) facts.callees facts.func facts.types
        (start facts.func facts.types) facts.state ∧
      closeFunction (lower module) facts.callees facts.func facts.types =
        if check (lower module) facts.func facts.types facts.state then some facts.state else none := by
  obtain ⟨callees, closed, finite, stable⟩ := accepted_module_close_finite accepted
  have native := lowerGlobal_canonical_facts_of_accepted accepted globalAt
  have moduleFacts := lower_canonical_facts_of_accepted accepted
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  have moduleBounds := close_canonicalWithin moduleFacts annotations entries addresses closed
  obtain ⟨state, reachable, stateFinite, fixed, outcome⟩ := accepted_global_solver_outcome accepted globalAt closed
  obtain ⟨upper, below, occurrences⟩ := accepted_global_instruction_occurrences accepted globalAt
  let facts : SourceReadyFunction := {
    source := ⟨module, Core.initImpl, Core.initContext, []⟩
    root := .expression global.init
    func := (lowerGlobal module global).init
    types := (lowerGlobal module global).init.valueTypes (lower module)
    provenance := (lowerGlobal module global).init.provenance
      (resultRoots (lower module) (lower module).implTypes)
      ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount
    upper := upper
    state := state
    completed := cfg_globalState module global
    moduleTypes := (lower module).funcs.map (·.valueTypes (lower module))
    moduleProvenances := (lower module).funcs.map fun func => func.provenance
      (resultRoots (lower module) (lower module).implTypes) (func.valueTypes (lower module)) (lower module).rootCount
    resultRoots := resultRoots (lower module) (lower module).implTypes
    callees := callees
    accepted := accepted
    caller := .global rfl rfl
    closed := closed
    moduleFacts := moduleFacts
    moduleBounds := moduleBounds.1
    frame := ⟨fixed, stateFinite.2, cfg_global_blocks module global, lowerGlobal_state_numValues module global⟩
    native := native
    canonical := reachable.canonicalWithin native.start native moduleFacts moduleBounds.1 finite.1
    growth := reachable.extends
    occurrences := occurrences
    below := below.vals
    slotCount := rfl
    slotSeeds := by intro variableId localVar row; simp [Core.initImpl] at row }
  exact ⟨facts, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, reachable, outcome⟩

#print axioms accepted_context_ready_inputs
#print axioms accepted_global_ready_inputs

end Goose.Lower.Validation.ReplacementContentFlowSource
