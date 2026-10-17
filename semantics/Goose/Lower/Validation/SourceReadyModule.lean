import Goose.Lower.Validation.SourceReadyCanonicalModuleInputs
import Goose.Lower.Validation.SourceReadyCompleted
import Goose.Lower.Validation.SourceReadyNormalizedInputs
import Goose.Lower.Validation.SourceReadyCheckCalls
import Goose.GIR.ReplacementContentFlowProofsAssignedOriginsStages

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_module_completed_ready_inputs {module : Core.Module} {states : Array State}
    (accepted : Core.validate module = .ok ())
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states)
    {index : Nat} {func : Func} {state : State}
    (funcAt : (lower module).funcs[index]? = some func) (stateAt : states[index]? = some state) :
    ∃ facts : SourceReadyFunction,
      facts.source.mod = module ∧ facts.func = func ∧ facts.state = state ∧ facts.callees = states ∧
      SourceReadyBuilder facts.state facts.completed ∧
      ∀ instruction ∈ facts.completed.insts,
        ReadyCallObservations (lower facts.source.mod) facts.func facts.state instruction := by
  obtain ⟨context, impl, contextAt, implAt, function⟩ := accepted_function_context accepted funcAt
  obtain ⟨facts, sourceEq, rootEq, functionEq, typesEq, provenanceEq, completedEq,
      moduleTypesEq, resultRootsEq, calleesEq, stateEq⟩ :=
    accepted_context_module_ready_inputs accepted contextAt implAt closed stateAt
  have ready := facts.context_completed sourceEq functionEq typesEq completedEq contextAt implAt
  exact ⟨facts, congrArg PEnv.mod sourceEq, functionEq.trans function.symm, stateEq, calleesEq, ready⟩

theorem accepted_module_assigned_nonpending {module : Core.Module} {states : Array State}
    (accepted : Core.validate module = .ok ())
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states) :
    ∀ (index : Nat) (func : Func) (state : State), (lower module).funcs[index]? = some func →
      states[index]? = some state → ∀ (parameter : Nat) (roots : Roots),
        state.writes[parameter]? = some (.assigned roots) → roots ≠ .pending := by
  apply ModuleReachable.assigned_nonpending (close_reachable closed) (close_fixed closed)
  · intro index func state funcAt stateAt block blockMember instruction instructionMember value use
    obtain ⟨facts, sourceEq, functionEq, stateEq, calleesEq, ready, observed⟩ :=
      accepted_module_completed_ready_inputs accepted closed funcAt stateAt
    have known := facts.normalized_operands ready (functionEq ▸ blockMember) instructionMember use
    simpa only [functionEq, stateEq] using known
  · intro index func funcAt block blockMember value calleeId arguments origin called
    have bounded : index < states.size := by
      have sizes := (close_initial_extends closed).size
      have bound := (Array.getElem?_eq_some_iff.mp funcAt).1
      have initialBound : index < (moduleStart (lower module)
          ((lower module).funcs.map (·.valueTypes (lower module)))).size := by
        simpa only [moduleStart, Array.size_mapIdx] using bound
      exact sizes ▸ initialBound
    have stateAt : states[index]? = some states[index] := Array.getElem?_eq_getElem bounded
    obtain ⟨facts, sourceEq, functionEq, stateEq, calleesEq, ready, observed⟩ :=
      accepted_module_completed_ready_inputs accepted closed funcAt stateAt
    simpa only [sourceEq] using facts.call_arity (functionEq ▸ blockMember) called
  · intro index func state funcAt stateAt block blockMember value calleeId arguments origin called
      callee calleeAt parameter declared argument argumentAt
    obtain ⟨facts, sourceEq, functionEq, stateEq, calleesEq, ready, observed⟩ :=
      accepted_module_completed_ready_inputs accepted closed funcAt stateAt
    have known := facts.observed_contents observed (functionEq ▸ blockMember) called
      (by simpa only [sourceEq] using calleeAt) declared argumentAt
    simpa only [functionEq, stateEq] using known
  · intro index func state funcAt stateAt parameter roots written
    obtain ⟨facts, sourceEq, functionEq, stateEq, calleesEq, ready, observed⟩ :=
      accepted_module_completed_ready_inputs accepted closed funcAt stateAt
    have safe := facts.write_safety (by simpa only [stateEq] using written)
    simpa only [functionEq] using safe

#print axioms accepted_module_completed_ready_inputs
#print axioms accepted_module_assigned_nonpending

end Goose.Lower.Validation.ReplacementContentFlowSource
