import Goose.Proofs.ConstructionAcceptedParameterObservation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

theorem bindAll_single_lookup (activation : RuntimeActivation) (scope : Nat) (parameter : Nat) (value : Value)
    (before after : ExecutionState)
    (bound : bindAll activation.act before.nextScope [(parameter, value)]
      (ownershipResultScopeState activation scope { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }) = .ok () after) :
    after.objects.lookup (.local activation.act before.nextScope parameter) = some value := by
  let scopeState := ownershipResultScopeState activation scope { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }
  cases step : bindRoot (.local activation.act before.nextScope parameter) value scopeState with
  | stop reason state | escape reason carriers state | jump target kind state =>
    simp [bindAll, List.forIn_cons, bind, pure, scopeState, step] at bound
  | ok result state =>
    cases result
    have same : state = after := by simpa [bindAll, List.forIn_cons, bind, pure, scopeState, step] using bound
    subst state
    obtain ⟨final, executed, objects⟩ := bindRoot_objects (.local activation.act before.nextScope parameter) value scopeState
    rw [step] at executed
    cases executed
    rw [objects]
    simp

#print axioms bindAll_single_lookup
end Goose.Proofs.ConstructionAcceptedExecution
