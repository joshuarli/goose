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

theorem AcceptedFrame.uninitializedLocals_afterFreshActivation
    {config : EvalConfig} {accepted : AcceptedModule config} {frame : ConstructionSourceFrame}
    {state after : ExecutionState} {types nextTypes : RootTypes} {initialized : Nat}
    {ambient : OwnershipAmbient} {live : Goose.Core.RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (source : AcceptedFrame config accepted frame state types)
    (preserved : ∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local state.nextAct scope id) → nextTypes root = types root)
    (world : AcceptedWorld config initialized after ambient nextTypes live regions pending) :
    ∀ id, frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing → ∀ root,
      rootOf frame.interpretation.environment id state = .ok root state →
        rootOf frame.interpretation.environment id after = .ok root after ∧ nextTypes root = none ∧
        after.objects.lookup root = none ∧ after.objectOrdinals.lookup root = none := by
  intro id uninitialized root resolved
  have absent := source.uninitializedTypes_afterFreshActivation preserved id uninitialized root resolved
  refine ⟨rootOf_transfer frame.interpretation id state after root resolved, absent, ?_, ?_⟩
  · cases found : after.objects.lookup root with
    | none => rfl
    | some value =>
      obtain ⟨ty, declared⟩ := world.objectsRegistered root value found
      rw [absent] at declared
      cases declared
  · cases found : after.objectOrdinals.lookup root with
    | none => rfl
    | some ordinal =>
      obtain ⟨ty, declared⟩ := world.ordinalsRegistered root ordinal found
      rw [absent] at declared
      cases declared

#print axioms AcceptedFrame.uninitializedLocals_afterFreshActivation
#print axioms AcceptedFrame.uninitializedTypes_afterFreshActivation
end Goose.Proofs.ConstructionAcceptedExecution
