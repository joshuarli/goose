import Goose.Lower.Validation.SourceReadyModule
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyWrites
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReturns
import Goose.Lower.Validation.ReplacementContentFlowSourceAnnotations

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_module_checkWrites {module : Core.Module} {states : Array State}
    (accepted : Core.validate module = .ok ())
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states)
    {index : Nat} {func : Func} {state : State}
    (funcAt : (lower module).funcs[index]? = some func) (stateAt : states[index]? = some state) :
    checkWrites func state = true := by
  obtain ⟨facts, sourceEq, functionEq, stateEq, calleesEq, ready, observed⟩ :=
    accepted_module_completed_ready_inputs accepted closed funcAt stateAt
  rw [← functionEq, ← stateEq]
  exact checkWrites_of_canonical facts.canonical facts.native.roots.closed facts.native.roots.unique
    (by simpa only [functionEq, stateEq] using (accepted_module_assigned_nonpending accepted closed
      index func state funcAt stateAt))

theorem accepted_context_checkReturned {module : Core.Module} {context : Context} {impl : Impl}
    {index : Nat} {state : State}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    (canonical : state.CanonicalWithin (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))
      ((lowerContextAt module context impl).provenance (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount))
    (growth : (start (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).Extends state) :
    checkReturned (lowerContextAt module context impl) state = true := by
  have native := lowerContext_canonical_facts_of_accepted accepted contextAt implAt
  apply checkReturned_of_initial_extends canonical native.roots.closed growth
  · obtain ⟨bodyType, finish, typed, resultShape⟩ := (validate_modOk module accepted).impl context.impl impl implAt |>.body
    rcases resultShape with ⟨empty, _⟩ | ⟨type, single, _⟩
    · exact Or.inl (by simpa only [lowerContextAt, lowerImpl, lowerImplFromState] using empty)
    · exact Or.inr ⟨type, by simpa only [lowerContextAt, lowerImpl, lowerImplFromState] using single⟩
  · intro type single reference
    have size := (lowerContextAt_symbol_tables accepted contextAt implAt).resultRows
    have bound : 0 < (lowerContextAt module context impl).roots.results.size := by
      rw [size, single]
      simp only [List.length_singleton, Nat.zero_lt_succ]
    exact ⟨_, Array.getElem?_eq_getElem bound⟩

theorem accepted_module_checkReturned {module : Core.Module} {states : Array State}
    (accepted : Core.validate module = .ok ())
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states)
    {index : Nat} {func : Func} {state : State}
    (funcAt : (lower module).funcs[index]? = some func) (stateAt : states[index]? = some state) :
    checkReturned func state = true := by
  obtain ⟨context, impl, contextAt, implAt, function⟩ := accepted_function_context accepted funcAt
  obtain ⟨facts, sourceEq, rootEq, functionEq, typesEq, provenanceEq, completedEq,
      moduleTypesEq, resultRootsEq, calleesEq, stateEq⟩ :=
    accepted_context_module_ready_inputs accepted contextAt implAt closed stateAt
  rw [function]
  apply accepted_context_checkReturned accepted contextAt implAt
  · simpa only [functionEq, typesEq, provenanceEq, stateEq] using facts.canonical
  · simpa only [functionEq, typesEq, stateEq] using facts.growth

#print axioms accepted_module_checkWrites
#print axioms accepted_context_checkReturned
#print axioms accepted_module_checkReturned

end Goose.Lower.Validation.ReplacementContentFlowSource
