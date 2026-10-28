import Goose.Proofs.ConstructionAcceptedCallerContents
import Goose.Proofs.ConstructionAcceptedScalarWriteFrame

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem AcceptedFrame.afterFreshActivationWithScalarGlobals
    {config : EvalConfig} {accepted : AcceptedModule config} {frame : ConstructionSourceFrame}
    {state after : ExecutionState} {types nextTypes : RootTypes}
    (source : AcceptedFrame config accepted frame state types)
    (initialized : frame.initialized = config.module.globals.size)
    (acts : state.nextAct ≤ after.nextAct) (scopes : state.nextScope ≤ after.nextScope)
    (objects : ∀ root, (∀ scope id, root ≠ .local state.nextAct scope id) →
      after.objects.lookup root = state.objects.lookup root ∨
      ∃ id value, root = .global id ∧ after.objects.lookup root = some value ∧
        ((∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean))
    (ordinals : ∀ root, (∀ scope id, root ≠ .local state.nextAct scope id) →
      after.objectOrdinals.lookup root = state.objectOrdinals.lookup root)
    (typesPreserved : ∀ root, (∀ scope id, root ≠ .local state.nextAct scope id) → nextTypes root = types root) :
    AcceptedFrame config accepted frame after nextTypes := by
  have localOutside : ∀ id root, rootOf frame.interpretation.environment id state = .ok root state →
      ∀ scope other, root ≠ Goose.Core.RootInst.local state.nextAct scope other := by
    intro id root resolved scope other same
    obtain ⟨actualScope, localRoot⟩ := rootOf_variable frame.interpretation id state root resolved
    rw [localRoot] at same
    exact (Nat.ne_of_lt source.frontier.1) (Goose.Core.RootInst.local.inj same).1
  have localObjects : ∀ id root, rootOf frame.interpretation.environment id state = .ok root state →
      after.objects.lookup root = state.objects.lookup root := by
    intro id root resolved
    rcases objects root (localOutside id root resolved) with unchanged | ⟨globalId, value, global, found, scalar⟩
    · exact unchanged
    · obtain ⟨scope, localRoot⟩ := rootOf_variable frame.interpretation id state root resolved
      rw [localRoot] at global
      cases global
  have content : ∀ fuel, ContentRootCorrespondence frame.interpretation frame.source.ctx frame.typing.visible fuel config.layout after := by
    intro fuel id visible roots found root location value resolved present read interior reference
    have prior := rootOf_transfer frame.interpretation id after state root resolved
    have oldPresent := (localObjects id root prior).symm.trans present
    have rooted := source.direct id visible root (.ref location) prior oldPresent location (.reference location)
    obtain ⟨symbolicRoots, _, symbolic, member, instantiated⟩ := rooted
    have outside : ∀ scope id', location.root ≠ Goose.Core.RootInst.local state.nextAct scope id' := by
      intro scope id' same
      have localInst := instantiated
      rw [same] at localInst
      exact (Nat.ne_of_lt (instantiates_before source.frontier symbolic state.nextAct scope id' localInst)) rfl
    rcases objects location.root outside with unchanged | ⟨globalId, scalarValue, global, foundScalar, scalar⟩
    · have oldRead := readLoc_directReference_transfer fuel config.layout location after state value interior unchanged.symm read reference
      exact source.contents fuel id visible roots found root location value prior oldPresent oldRead interior reference
    · exact (readLoc_scalarRoot_noReference fuel config.layout after location scalarValue value interior scalar foundScalar read reference).elim
  refine ⟨source.compatible, ⟨Nat.lt_of_lt_of_le source.frontier.1 acts, source.frontier.2⟩,
    ?_, source.initializingBefore, source.aliases, ?_, ?_, ?_, ?_, ?_, ?_, content⟩
  · intro entry member
    exact Nat.lt_of_lt_of_le (source.scopeFrontier entry member) scopes
  · intro id visible
    obtain ⟨descriptor, root, value, declared, resolved, found, represented⟩ := source.locals id visible
    exact ⟨descriptor, root, value, declared, rootOf_transfer frame.interpretation id state after root resolved,
      (localObjects id root resolved).trans found, represented⟩
  · intro id visible descriptor root declared resolved
    have prior := rootOf_transfer frame.interpretation id after state root resolved
    rw [typesPreserved root (localOutside id root prior)]
    exact source.localTypes id visible descriptor root declared prior
  · intro id uninitialized root resolved
    have prior := rootOf_transfer frame.interpretation id after state root resolved
    exact ⟨(localObjects id root prior).trans (source.uninitializedLocals id uninitialized root prior).1,
      (ordinals root (localOutside id root prior)).trans (source.uninitializedLocals id uninitialized root prior).2⟩
  · intro id uninitialized root resolved
    have prior := rootOf_transfer frame.interpretation id after state root resolved
    rw [typesPreserved root (localOutside id root prior)]
    exact source.uninitializedTypes id uninitialized root prior
  · intro id lower upper
    rw [initialized] at lower
    omega
  · intro id visible root value resolved found
    have prior := rootOf_transfer frame.interpretation id after state root resolved
    have oldFound := (localObjects id root prior).symm.trans found
    exact source.direct id visible root value prior oldFound

#print axioms AcceptedFrame.afterFreshActivationWithScalarGlobals
end Goose.Proofs.ConstructionAcceptedExecution
