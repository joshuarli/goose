import Goose.Proofs.ConstructionAcceptedTwoScalarBinding
import Goose.Proofs.ConstructionAcceptedBindingCounters
import Goose.Proofs.ConstructionRootCorrespondenceWrites

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem bindAll_two_steps (act scope first second : Nat) (firstValue secondValue : Value)
    (before after : ExecutionState)
    (bound : bindAll act scope [(first, firstValue), (second, secondValue)] before = .ok () after) :
    ∃ middle, bindRoot (.local act scope first) firstValue before = .ok () middle ∧
      bindRoot (.local act scope second) secondValue middle = .ok () after := by
  cases firstStep : bindRoot (.local act scope first) firstValue before with
  | stop reason state | escape address carriers state | jump target kind state =>
    simp [bindAll, List.forIn_cons, bind, pure, firstStep] at bound
  | ok result middle =>
    cases result
    cases secondStep : bindRoot (.local act scope second) secondValue middle with
    | stop reason state | escape address carriers state | jump target kind state =>
      simp [bindAll, List.forIn_cons, bind, pure, firstStep, secondStep] at bound
    | ok result final =>
      cases result
      have same : final = after := by simpa [bindAll, List.forIn_cons, bind, pure, firstStep, secondStep] using bound
      subst final
      exact ⟨middle, rfl, secondStep⟩

theorem bindAll_two_observations (act scope first second : Nat) (firstValue secondValue : Value)
    (before after : ExecutionState)
    (bound : bindAll act scope [(first, firstValue), (second, secondValue)] before = .ok () after) :
    after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope ∧
      ∀ other, other ≠ .local act scope first → other ≠ .local act scope second →
        after.objects.lookup other = before.objects.lookup other ∧
        after.objectOrdinals.lookup other = before.objectOrdinals.lookup other := by
  obtain ⟨middle, firstStep, secondStep⟩ := bindAll_two_steps act scope first second firstValue secondValue before after bound
  have firstCounters := bindRoot_counters _ firstValue before middle firstStep
  have secondCounters := bindRoot_counters _ secondValue middle after secondStep
  refine ⟨secondCounters.1.trans firstCounters.1, secondCounters.2.trans firstCounters.2, ?_⟩
  intro other firstDifferent secondDifferent
  exact ⟨(bindRoot_lookup_other _ other secondValue middle after secondStep secondDifferent).trans
      (bindRoot_lookup_other _ other firstValue before middle firstStep firstDifferent),
    (bindRoot_ordinals_other _ other secondValue middle after secondStep secondDifferent).trans
      (bindRoot_ordinals_other _ other firstValue before middle firstStep firstDifferent)⟩

#print axioms bindAll_two_steps
#print axioms bindAll_two_observations
end Goose.Proofs.ConstructionAcceptedExecution
