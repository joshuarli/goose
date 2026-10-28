import Goose.Proofs.ConstructionAcceptedTwoParameterObservation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem bindAll_list_observations (act scope : Nat) (bindings : List (Nat × Value)) (before after : ExecutionState)
    (bound : bindAll act scope bindings before = .ok () after) :
    after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope ∧
      ∀ other, (∀ id, other ≠ .local act scope id) →
        after.objects.lookup other = before.objects.lookup other ∧
        after.objectOrdinals.lookup other = before.objectOrdinals.lookup other := by
  induction bindings generalizing before with
  | nil =>
    have same : after = before := by simpa [bindAll, pure, bind] using bound.symm
    subst after
    exact ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  | cons binding rest ih =>
    obtain ⟨id, value⟩ := binding
    cases firstStep : bindRoot (.local act scope id) value before with
    | stop reason middle | escape address carriers middle | jump target kind middle =>
      simp [bindAll, List.forIn_cons, bind, pure, firstStep] at bound
    | ok result middle =>
      cases result
      have tail : bindAll act scope rest middle = .ok () after := by
        simpa [bindAll, List.forIn_cons, bind, pure, firstStep] using bound
      have firstCounters := bindRoot_counters _ value before middle firstStep
      obtain ⟨nextAct, nextScope, outside⟩ := ih middle tail
      refine ⟨nextAct.trans firstCounters.1, nextScope.trans firstCounters.2, ?_⟩
      intro other different
      obtain ⟨object, ordinal⟩ := outside other different
      exact ⟨object.trans (bindRoot_lookup_other _ other value before middle firstStep (different id)),
        ordinal.trans (bindRoot_ordinals_other _ other value before middle firstStep (different id))⟩

#print axioms bindAll_list_observations
end Goose.Proofs.ConstructionAcceptedExecution
