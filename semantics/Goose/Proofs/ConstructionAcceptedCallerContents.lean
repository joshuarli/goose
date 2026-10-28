import Goose.Proofs.ConstructionAcceptedCallerTypePreservation
import Goose.Proofs.ConstructionRootCorrespondenceReads

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private theorem callerLocal_outside {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (id : Nat) (root : Goose.Core.RootInst)
    (resolved : rootOf frame.interpretation.environment id state = .ok root state) :
    ∀ scope id, root ≠ .local state.nextAct scope id := by
  obtain ⟨scope, localRoot⟩ := rootOf_variable frame.interpretation id state root resolved
  intro scope' id' same
  rw [localRoot] at same
  exact (Nat.ne_of_lt source.frontier.1) (Goose.Core.RootInst.local.inj same).1

theorem AcceptedFrame.contents_afterFreshActivation
    {config : EvalConfig} {accepted : AcceptedModule config} {frame : ConstructionSourceFrame}
    {state after : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types)
    (objects : ∀ root, (∀ scope id, root ≠ .local state.nextAct scope id) →
      after.objects.lookup root = state.objects.lookup root) :
    ∀ fuel, ContentRootCorrespondence frame.interpretation frame.source.ctx
      frame.typing.visible fuel config.layout after := by
  intro fuel id visible roots found root location value resolved present read interior reference
  have prior := rootOf_transfer frame.interpretation id after state root resolved
  have oldPresent := (objects root (callerLocal_outside source id root prior)).symm.trans present
  have rooted := source.direct id visible root (.ref location) prior oldPresent location (.reference location)
  obtain ⟨symbolicRoots, _, symbolic, member, instantiated⟩ := rooted
  have outside : ∀ scope id', location.root ≠ .local state.nextAct scope id' := by
    intro scope id' same
    have localInst := instantiated
    rw [same] at localInst
    exact (Nat.ne_of_lt (instantiates_before source.frontier symbolic state.nextAct scope id' localInst)) rfl
  have oldRead := readLoc_directReference_transfer fuel config.layout location after state value interior
    (objects location.root outside).symm read reference
  exact source.contents fuel id visible roots found root location value prior oldPresent oldRead interior reference

theorem AcceptedFrame.afterFreshActivation
    {config : EvalConfig} {accepted : AcceptedModule config} {frame : ConstructionSourceFrame}
    {state after : ExecutionState} {types nextTypes : RootTypes}
    (source : AcceptedFrame config accepted frame state types)
    (acts : state.nextAct ≤ after.nextAct) (scopes : state.nextScope ≤ after.nextScope)
    (objects : ∀ root, (∀ scope id, root ≠ .local state.nextAct scope id) →
      after.objects.lookup root = state.objects.lookup root)
    (ordinals : ∀ root, (∀ scope id, root ≠ .local state.nextAct scope id) →
      after.objectOrdinals.lookup root = state.objectOrdinals.lookup root)
    (typesPreserved : ∀ root, (∀ scope id, root ≠ .local state.nextAct scope id) → nextTypes root = types root) :
    AcceptedFrame config accepted frame after nextTypes := by
  refine ⟨source.compatible, ⟨Nat.lt_of_lt_of_le source.frontier.1 acts, source.frontier.2⟩,
    ?_, source.initializingBefore, source.aliases, ?_, ?_, ?_, ?_, ?_, ?_,
    source.contents_afterFreshActivation objects⟩
  · intro entry member
    exact Nat.lt_of_lt_of_le (source.scopeFrontier entry member) scopes
  · intro id visible
    obtain ⟨descriptor, root, value, declared, resolved, found, represented⟩ := source.locals id visible
    exact ⟨descriptor, root, value, declared, rootOf_transfer frame.interpretation id state after root resolved,
      (objects root (callerLocal_outside source id root resolved)).trans found, represented⟩
  · intro id visible descriptor root declared resolved
    have prior := rootOf_transfer frame.interpretation id after state root resolved
    rw [typesPreserved root (callerLocal_outside source id root prior)]
    exact source.localTypes id visible descriptor root declared prior
  · intro id uninitialized root resolved
    have prior := rootOf_transfer frame.interpretation id after state root resolved
    exact ⟨(objects root (callerLocal_outside source id root prior)).trans (source.uninitializedLocals id uninitialized root prior).1,
      (ordinals root (callerLocal_outside source id root prior)).trans (source.uninitializedLocals id uninitialized root prior).2⟩
  · intro id uninitialized root resolved
    have prior := rootOf_transfer frame.interpretation id after state root resolved
    rw [typesPreserved root (callerLocal_outside source id root prior)]
    exact source.uninitializedTypes id uninitialized root prior
  · intro id lower upper
    have outside : ∀ scope id', Goose.Core.RootInst.global id ≠ .local state.nextAct scope id' := by intro scope id' equal; cases equal
    exact ⟨(objects _ outside).trans (source.futureGlobals id lower upper).1,
      (ordinals _ outside).trans (source.futureGlobals id lower upper).2⟩
  · intro id visible root value resolved found
    have prior := rootOf_transfer frame.interpretation id after state root resolved
    have oldFound := (objects root (callerLocal_outside source id root prior)).symm.trans found
    exact source.direct id visible root value prior oldFound

#print axioms AcceptedFrame.afterFreshActivation
#print axioms AcceptedFrame.contents_afterFreshActivation
end Goose.Proofs.ConstructionAcceptedExecution
