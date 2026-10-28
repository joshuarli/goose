import Goose.Proofs.ConstructionAcceptedSourceAssignObservation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

def ScalarGlobalObservation (act : Nat) (before after : ExecutionState) : Prop :=
  after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope ∧
    (∀ root, (∀ scope id, root ≠ .local act scope id) →
      after.objects.lookup root = before.objects.lookup root ∨
      ∃ id value, root = .global id ∧ after.objects.lookup root = some value ∧
        ((∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean)) ∧
    (∀ otherAct scope id, otherAct ≠ act →
      after.objectOrdinals.lookup (.local otherAct scope id) = before.objectOrdinals.lookup (.local otherAct scope id))

theorem ScalarGlobalObservation.refl (act : Nat) (state : ExecutionState) : ScalarGlobalObservation act state state := by
  exact ⟨rfl, rfl, fun _ _ => Or.inl rfl, fun _ _ _ _ => rfl⟩

theorem ScalarGlobalObservation.trans {act : Nat} {before middle after : ExecutionState}
    (first : ScalarGlobalObservation act before middle) (second : ScalarGlobalObservation act middle after) :
    ScalarGlobalObservation act before after := by
  refine ⟨second.1.trans first.1, second.2.1.trans first.2.1, ?_, ?_⟩
  · intro root outside
    rcases second.2.2.1 root outside with afterSame | afterScalar
    · rcases first.2.2.1 root outside with middleSame | ⟨id, value, global, found, scalar⟩
      · exact Or.inl (afterSame.trans middleSame)
      · exact Or.inr ⟨id, value, global, afterSame.trans found, scalar⟩
    · exact Or.inr afterScalar
  · intro otherAct scope id different
    exact (second.2.2.2 otherAct scope id different).trans (first.2.2.2 otherAct scope id different)

theorem ScalarAssignmentObservation.globalSuccess {before after : ExecutionState} {id : Nat} {flow : Flow}
    (act : Nat) (observation : ScalarAssignmentObservation before (.global id) (.ok flow after)) :
    ScalarGlobalObservation act before after := by
  obtain ⟨acts, scopes, outside, value, found, scalar⟩ := observation
  refine ⟨acts, scopes, ?_, ?_⟩
  · intro root protectedRoot
    by_cases same : root = .global id
    · subst root
      exact Or.inr ⟨id, value, rfl, found, scalar⟩
    · exact Or.inl (outside root same).1
  · intro otherAct scope localId different
    exact (outside (.local otherAct scope localId) (by intro impossible; cases impossible)).2

theorem ScalarAssignmentObservation.localSuccess {before after : ExecutionState} {act scope id : Nat} {flow : Flow}
    (observation : ScalarAssignmentObservation before (.local act scope id) (.ok flow after)) :
    ScalarGlobalObservation act before after := by
  obtain ⟨acts, scopes, outside, value, found, scalar⟩ := observation
  refine ⟨acts, scopes, ?_, ?_⟩
  · intro root protectedRoot
    exact Or.inl (outside root (protectedRoot scope id)).1
  · intro otherAct otherScope localId different
    apply (outside (.local otherAct otherScope localId) ?_).2
    intro equal
    exact different (Goose.Core.RootInst.local.inj equal).1

#print axioms ScalarGlobalObservation.refl
#print axioms ScalarGlobalObservation.trans
#print axioms ScalarAssignmentObservation.globalSuccess
#print axioms ScalarAssignmentObservation.localSuccess
end Goose.Proofs.ConstructionAcceptedExecution
