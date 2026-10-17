import Goose.Lower.Validation.SourceReadyModuleCheck
import Goose.Lower.Validation.SourceReadyLocalWrites

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_context_closeFunction {module : Core.Module} {states : Array State}
    {context : Context} {impl : Impl} {index : Nat}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states) :
    ∃ state, closeFunction (lower module) states (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module)) = some state := by
  obtain ⟨facts, sourceEq, rootEq, functionEq, typesEq, provenanceEq, completedEq,
      moduleTypesEq, resultRootsEq, reachable, outcome⟩ :=
    accepted_context_ready_inputs accepted contextAt implAt
  have modelTypes : facts.moduleTypes =
      (lower facts.source.mod).funcs.map (·.valueTypes (lower facts.source.mod)) := by
    simpa only [sourceEq] using moduleTypesEq
  have sameClosure : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) =
      some facts.callees := by
    simpa only [sourceEq, moduleTypesEq] using facts.closed
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
  refine ⟨facts.state, ?_⟩
  simpa only [calleesEq, functionEq, typesEq, ↓reduceIte] using outcome

#print axioms accepted_context_closeFunction

end Goose.Lower.Validation.ReplacementContentFlowSource
