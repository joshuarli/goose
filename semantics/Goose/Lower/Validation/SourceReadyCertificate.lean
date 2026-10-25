import Goose.Lower.Validation.SourceReadyLocalCheck
import Goose.Lower.Validation.SourceReadyGlobalCheck

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_module_certificate {module : Core.Module} {states : Array State}
    (accepted : Core.validate module = .ok ())
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states) :
    certificate (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) states = true := by
  simp only [certificate, accepted_entry_shape accepted, Bool.true_and, Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    rintro ⟨func, index⟩ member
    have funcAt : (lower module).funcs[index]? = some func := by
      simpa only [Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp member
    have bound := (Array.getElem?_eq_some_iff.mp funcAt).1
    have initialBound : index < (moduleStart (lower module)
        ((lower module).funcs.map (·.valueTypes (lower module)))).size := by
      simpa only [moduleStart, Array.size_mapIdx] using bound
    have bounded : index < states.size := (close_initial_extends closed).size ▸ initialBound
    have stateAt : states[index]? = some states[index] := Array.getElem?_eq_getElem bounded
    have checked := accepted_module_model_check accepted closed funcAt stateAt
    simpa only [Array.getElem?_map, funcAt, Option.map_some, Option.getD_some, stateAt,
      Option.any_some] using checked
  · apply Array.all_eq_true.mpr
    intro index bounded
    have sourceBound : index < module.globals.size := by simpa only [lower, Array.size_map] using bounded
    let source := module.globals[index]
    have sourceAt : module.globals[index]? = some source := Array.getElem?_eq_getElem sourceBound
    have globalAt : (lower module).globals[index] = lowerGlobal module source := by
      simp only [lower, Array.getElem_map, source]
    obtain ⟨state, built⟩ := accepted_global_closeFunction accepted sourceAt closed
    rw [globalAt]
    have parameters : (lowerGlobal module source).init.params = [] := rfl
    have results : (lowerGlobal module source).init.results = [(lowerGlobal module source).ty] := rfl
    simp only [parameters, results, List.isEmpty_nil, beq_self_eq_true, built, Option.isSome_some,
      Bool.and_self]

theorem accepted_factory_model {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    ∃ states, (replacementContentFlow (lower module)).model = some states := by
  obtain ⟨states, closed, finite, stable⟩ := accepted_module_close_finite accepted
  refine ⟨states, ?_⟩
  rw [replacementContentFlow_model]
  simp only [accepted_storageClosed accepted, ↓reduceIte, closed, Option.filter_some,
    accepted_module_certificate accepted closed, ↓reduceIte]

theorem accepted_context_factory_model {module : Core.Module} {context : Context} {impl : Impl}
    {index : Nat} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    ∃ state, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).model = some state := by
  obtain ⟨states, built⟩ := accepted_factory_model accepted
  have closed := (replacementContentFlow_model_checked built).2.1
  obtain ⟨state, functionBuilt⟩ := accepted_context_closeFunction accepted contextAt implAt closed
  refine ⟨state, ?_⟩
  rw [ReplacementContentFlow.forFunction_model]
  simp only [replacementContentFlow_source, beq_self_eq_true, ↓reduceIte, built, Option.bind_some,
    functionBuilt]

theorem accepted_global_factory_model {module : Core.Module} {global : Core.Global}
    {index : Nat} (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global) :
    ∃ state, ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))).model = some state := by
  obtain ⟨states, built⟩ := accepted_factory_model accepted
  have closed := (replacementContentFlow_model_checked built).2.1
  obtain ⟨state, functionBuilt⟩ := accepted_global_closeFunction accepted globalAt closed
  refine ⟨state, ?_⟩
  rw [ReplacementContentFlow.forFunction_model]
  simp only [replacementContentFlow_source, beq_self_eq_true, ↓reduceIte, built, Option.bind_some,
    functionBuilt]

#print axioms accepted_module_certificate
#print axioms accepted_factory_model
#print axioms accepted_context_factory_model
#print axioms accepted_global_factory_model

end Goose.Lower.Validation.ReplacementContentFlowSource
