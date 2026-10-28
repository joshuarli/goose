import Goose.Proofs.ConstructionAcceptedRegisterParameterInvoke

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem AcceptedFrame.uninitializedTypes_afterFreshActivation
    {config : EvalConfig} {accepted : AcceptedModule config} {frame : ConstructionSourceFrame}
    {state : ExecutionState} {types nextTypes : RootTypes}
    (source : AcceptedFrame config accepted frame state types)
    (preserved : ∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local state.nextAct scope id) → nextTypes root = types root) :
    ∀ id, frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing → ∀ root,
      rootOf frame.interpretation.environment id state = .ok root state → nextTypes root = none := by
  intro id uninitialized root resolved
  obtain ⟨scope, localRoot⟩ := rootOf_variable frame.interpretation id state root resolved
  have outside : ∀ scope' id', root ≠ Goose.Core.RootInst.local state.nextAct scope' id' := by
    intro scope' id' same
    rw [localRoot] at same
    have sameAct : frame.interpretation.environment.act = state.nextAct := (Goose.Core.RootInst.local.inj same).1
    exact (Nat.ne_of_lt source.frontier.1) sameAct
  rw [preserved root outside]
  exact source.uninitializedTypes id uninitialized root resolved

#print axioms AcceptedFrame.uninitializedTypes_afterFreshActivation
end Goose.Proofs.ConstructionAcceptedExecution
