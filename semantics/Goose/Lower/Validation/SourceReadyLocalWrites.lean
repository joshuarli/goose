import Goose.Lower.Validation.SourceReadyModule
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyWrites

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.assigned_nonpending (candidate : SourceReadyFunction)
    (moduleTypesEq : candidate.moduleTypes =
      (lower candidate.source.mod).funcs.map (·.valueTypes (lower candidate.source.mod)))
    (reachable : FunctionReachable (lower candidate.source.mod) candidate.callees candidate.func candidate.types
      (start candidate.func candidate.types) candidate.state)
    (ready : SourceReadyBuilder candidate.state candidate.completed)
    (observed : ∀ instruction ∈ candidate.completed.insts,
      ReadyCallObservations (lower candidate.source.mod) candidate.func candidate.state instruction) :
    ∀ (index : Nat) (roots : Roots), candidate.state.writes[index]? = some (.assigned roots) → roots ≠ .pending := by
  have closed : close (lower candidate.source.mod)
      ((lower candidate.source.mod).funcs.map (·.valueTypes (lower candidate.source.mod))) =
      some candidate.callees := by
    rw [← moduleTypesEq]
    exact candidate.closed
  apply FunctionReachable.assigned_nonpending (close_reachable closed) (close_fixed closed)
      (reachable := reachable) (stable := candidate.frame.fixed)
  · intro index func state funcAt stateAt block blockMember instruction instructionMember value use
    obtain ⟨facts, sourceEq, functionEq, stateEq, calleesEq, ready, observed⟩ :=
      accepted_module_completed_ready_inputs candidate.accepted closed funcAt stateAt
    have known := facts.normalized_operands ready (functionEq ▸ blockMember) instructionMember use
    simpa only [functionEq, stateEq] using known
  · intro index func funcAt block blockMember value calleeId arguments origin called
    have bound := (Array.getElem?_eq_some_iff.mp funcAt).1
    have initialBound : index < (moduleStart (lower candidate.source.mod)
        ((lower candidate.source.mod).funcs.map (·.valueTypes (lower candidate.source.mod)))).size := by
      simpa only [moduleStart, Array.size_mapIdx] using bound
    have bounded : index < candidate.callees.size := (close_initial_extends closed).size ▸ initialBound
    have stateAt : candidate.callees[index]? = some candidate.callees[index] := Array.getElem?_eq_getElem bounded
    obtain ⟨facts, sourceEq, functionEq, stateEq, calleesEq, ready, observed⟩ :=
      accepted_module_completed_ready_inputs candidate.accepted closed funcAt stateAt
    simpa only [sourceEq] using facts.call_arity (functionEq ▸ blockMember) called
  · intro index func state funcAt stateAt block blockMember value calleeId arguments origin called
      callee calleeAt parameter declared argument argumentAt
    obtain ⟨facts, sourceEq, functionEq, stateEq, calleesEq, ready, observed⟩ :=
      accepted_module_completed_ready_inputs candidate.accepted closed funcAt stateAt
    have known := facts.observed_contents observed (functionEq ▸ blockMember) called
      (by simpa only [sourceEq] using calleeAt) declared argumentAt
    simpa only [functionEq, stateEq] using known
  · intro index func state funcAt stateAt parameter roots written
    obtain ⟨facts, sourceEq, functionEq, stateEq, calleesEq, ready, observed⟩ :=
      accepted_module_completed_ready_inputs candidate.accepted closed funcAt stateAt
    have safe := facts.write_safety (by simpa only [stateEq] using written)
    simpa only [functionEq] using safe
  · intro block member instruction instructionMember value use
    exact candidate.normalized_operands ready member instructionMember use
  · intro block member value calleeId arguments origin called
    exact candidate.call_arity member called
  · intro block member value calleeId arguments origin called callee calleeAt parameter declared argument argumentAt
    exact candidate.observed_contents observed member called calleeAt declared argumentAt

theorem SourceReadyFunction.check_writes (candidate : SourceReadyFunction)
    (moduleTypesEq : candidate.moduleTypes =
      (lower candidate.source.mod).funcs.map (·.valueTypes (lower candidate.source.mod)))
    (reachable : FunctionReachable (lower candidate.source.mod) candidate.callees candidate.func candidate.types
      (start candidate.func candidate.types) candidate.state)
    (ready : SourceReadyBuilder candidate.state candidate.completed)
    (observed : ∀ instruction ∈ candidate.completed.insts,
      ReadyCallObservations (lower candidate.source.mod) candidate.func candidate.state instruction) :
    checkWrites candidate.func candidate.state = true :=
  checkWrites_of_canonical candidate.canonical candidate.native.roots.closed candidate.native.roots.unique
    (candidate.assigned_nonpending moduleTypesEq reachable ready observed)

#print axioms SourceReadyFunction.assigned_nonpending
#print axioms SourceReadyFunction.check_writes

end Goose.Lower.Validation.ReplacementContentFlowSource
