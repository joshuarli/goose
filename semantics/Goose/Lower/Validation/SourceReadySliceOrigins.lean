import Goose.Lower.Validation.SourceReadyQueryKnown
import Goose.GIR.ReplacementContentFlowProofsSliceCallObservation

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_module_call_observation_ready {module : Core.Module} {states : Array State}
    (accepted : Core.validate module = .ok ())
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states)
    {index : Nat} {func : Func} {state : State}
    (funcAt : (lower module).funcs[index]? = some func) (stateAt : states[index]? = some state)
    {block : GIR.Block} (member : block ∈ func.blocks.toList)
    {value calleeId : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts)
    {callee : Func} (calleeAt : (lower module).funcs[calleeId]? = some callee) :
    CallObservationReady callee func state arguments := by
  obtain ⟨context, impl, contextAt, implAt, function⟩ := accepted_function_context accepted funcAt
  obtain ⟨facts, sourceEq, rootEq, functionEq, typesEq, provenanceEq, completedEq,
      moduleTypesEq, resultRootsEq, calleesEq, stateEq⟩ :=
    accepted_context_module_ready_inputs accepted contextAt implAt closed stateAt
  obtain ⟨_, observed⟩ := facts.context_completed sourceEq functionEq typesEq completedEq contextAt implAt
  have actualObserved : ∀ instruction ∈ (cfg_implState module impl).insts,
      ReadyCallObservations (lower module) (lowerContextAt module context impl) state instruction := by
    simpa only [sourceEq, functionEq, stateEq, completedEq] using observed
  have completedMember : block ∈ (finishBlocks (cfg_implState module impl).blocks).toList := by
    rw [function, cfg_context_blocks] at member
    exact member
  have emitted := finishBlocks_instruction_member completedMember called
  have ready := actualObserved _ emitted value calleeId arguments origin rfl callee calleeAt
  simpa only [function] using ready

theorem accepted_module_slice_origins {module : Core.Module} {states : Array State}
    (accepted : Core.validate module = .ok ())
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states) :
    ModuleSliceOrigins (lower module) ((lower module).funcs.map (·.valueTypes (lower module)))
      (moduleTouchAtoms states) states := by
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  apply close_sliceOrigins (lower_canonical_facts_of_accepted accepted) annotations entries addresses closed
  intro index func state funcAt stateAt block member value calleeId args origin called callee calleeAt
  exact accepted_module_call_observation_ready accepted closed funcAt stateAt member called calleeAt

#print axioms accepted_module_call_observation_ready
#print axioms accepted_module_slice_origins

end Goose.Lower.Validation.ReplacementContentFlowSource
