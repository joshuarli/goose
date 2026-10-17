import Goose.Lower.Validation.SourceReadyCertificate

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_context_factory_ready_inputs {module : Core.Module} {context : Context} {impl : Impl}
    {index : Nat} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    ∃ facts : SourceReadyFunction,
      facts.source = ⟨module, impl, context, []⟩ ∧ facts.func = lowerContextAt module context impl ∧
      facts.types = (lowerContextAt module context impl).valueTypes (lower module) ∧
      facts.completed = cfg_implState module impl ∧
      ((replacementContentFlow (lower module)).forFunction facts.func facts.types).model = some facts.state ∧
      SourceReadyBuilder facts.state facts.completed ∧
      ∀ instruction ∈ facts.completed.insts,
        ReadyCallObservations (lower facts.source.mod) facts.func facts.state instruction := by
  obtain ⟨states, built⟩ := accepted_factory_model accepted
  have closed := (replacementContentFlow_model_checked built).2.1
  obtain ⟨facts, sourceEq, rootEq, functionEq, typesEq, provenanceEq, completedEq,
      moduleTypesEq, resultRootsEq, reachable, outcome⟩ :=
    accepted_context_ready_inputs accepted contextAt implAt
  have modelTypes : facts.moduleTypes =
      (lower facts.source.mod).funcs.map (·.valueTypes (lower facts.source.mod)) := by
    simpa only [sourceEq] using moduleTypesEq
  have sameClosure : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) =
      some facts.callees := by simpa only [sourceEq, moduleTypesEq] using facts.closed
  have calleesEq : facts.callees = states := Option.some.inj (sameClosure.symm.trans closed)
  have path : FunctionReachable (lower facts.source.mod) facts.callees facts.func facts.types
      (start facts.func facts.types) facts.state := by simpa only [sourceEq] using reachable
  obtain ⟨ready, observed⟩ := facts.context_completed sourceEq functionEq typesEq completedEq contextAt implAt
  have assigned := facts.assigned_nonpending modelTypes path ready observed
  have checked := facts.context_check sourceEq functionEq typesEq provenanceEq completedEq
    contextAt implAt ready observed assigned
  have actualCheck : check (lower module) facts.func facts.types facts.state = true := by
    simpa only [sourceEq] using checked
  rw [actualCheck] at outcome
  have model : ((replacementContentFlow (lower module)).forFunction facts.func facts.types).model =
      some facts.state := by
    rw [ReplacementContentFlow.forFunction_model]
    simp only [typesEq, functionEq, replacementContentFlow_source, beq_self_eq_true, ↓reduceIte,
      built, Option.bind_some]
    simpa only [calleesEq, functionEq, typesEq, ↓reduceIte] using outcome
  exact ⟨facts, sourceEq, functionEq, typesEq, completedEq, model, ready, observed⟩

theorem accepted_global_factory_ready_inputs {module : Core.Module} {global : Core.Global}
    {index : Nat} (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global) :
    ∃ facts : SourceReadyFunction,
      facts.source = ⟨module, initImpl, initContext, []⟩ ∧ facts.func = (lowerGlobal module global).init ∧
      facts.types = (lowerGlobal module global).init.valueTypes (lower module) ∧
      facts.completed = cfg_globalState module global ∧
      ((replacementContentFlow (lower module)).forFunction facts.func facts.types).model = some facts.state ∧
      SourceReadyBuilder facts.state facts.completed ∧
      ∀ instruction ∈ facts.completed.insts,
        ReadyCallObservations (lower facts.source.mod) facts.func facts.state instruction := by
  obtain ⟨states, built⟩ := accepted_factory_model accepted
  have closed := (replacementContentFlow_model_checked built).2.1
  obtain ⟨facts, sourceEq, rootEq, functionEq, typesEq, provenanceEq, completedEq,
      moduleTypesEq, resultRootsEq, reachable, outcome⟩ := accepted_global_ready_inputs accepted globalAt
  have modelTypes : facts.moduleTypes =
      (lower facts.source.mod).funcs.map (·.valueTypes (lower facts.source.mod)) := by
    simpa only [sourceEq] using moduleTypesEq
  have sameClosure : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) =
      some facts.callees := by simpa only [sourceEq, moduleTypesEq] using facts.closed
  have calleesEq : facts.callees = states := Option.some.inj (sameClosure.symm.trans closed)
  have path : FunctionReachable (lower facts.source.mod) facts.callees facts.func facts.types
      (start facts.func facts.types) facts.state := by simpa only [sourceEq] using reachable
  obtain ⟨ready, observed⟩ := facts.global_completed sourceEq typesEq completedEq globalAt
  have assigned := facts.assigned_nonpending modelTypes path ready observed
  have checked := facts.global_check sourceEq functionEq typesEq completedEq globalAt ready observed assigned
  have actualCheck : check (lower module) facts.func facts.types facts.state = true := by
    simpa only [sourceEq] using checked
  rw [actualCheck] at outcome
  have model : ((replacementContentFlow (lower module)).forFunction facts.func facts.types).model =
      some facts.state := by
    rw [ReplacementContentFlow.forFunction_model]
    simp only [typesEq, functionEq, replacementContentFlow_source, beq_self_eq_true, ↓reduceIte,
      built, Option.bind_some]
    simpa only [calleesEq, functionEq, typesEq, ↓reduceIte] using outcome
  exact ⟨facts, sourceEq, functionEq, typesEq, completedEq, model, ready, observed⟩

#print axioms accepted_context_factory_ready_inputs
#print axioms accepted_global_factory_ready_inputs

end Goose.Lower.Validation.ReplacementContentFlowSource
