import Goose.Proofs.ConstructionAcceptedRegisterParameterArgument
import Goose.Proofs.ConstructionAcceptedBindingCounters

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem bindAll_single_outside (activation : RuntimeActivation) (scope : Nat) (parameter : Nat) (value : Value)
    (before after : ExecutionState)
    (bound : bindAll activation.act before.nextScope [(parameter, value)]
      (ownershipResultScopeState activation scope { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }) = .ok () after)
    (other : Goose.Core.RootInst) (outside : ∀ scope id, other ≠ .local activation.act scope id) :
    after.objects.lookup other = before.objects.lookup other ∧
    after.objectOrdinals.lookup other = before.objectOrdinals.lookup other := by
  let scopeState := ownershipResultScopeState activation scope { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }
  cases step : bindRoot (.local activation.act before.nextScope parameter) value scopeState with
  | stop reason state | escape reason carriers state | jump target kind state =>
    simp [bindAll, List.forIn_cons, bind, pure, scopeState, step] at bound
  | ok result state =>
    cases result
    have same : state = after := by simpa [bindAll, List.forIn_cons, bind, pure, scopeState, step] using bound
    subst state
    have objects := bindRoot_lookup_other _ other value scopeState after step (outside before.nextScope parameter)
    have ordinals := bindRoot_ordinals_other _ other value scopeState after step (outside before.nextScope parameter)
    exact ⟨by simpa [scopeState, ownershipResultScopeState] using objects,
      by simpa [scopeState, ownershipResultScopeState] using ordinals⟩

theorem bindAll_single_counters (activation : RuntimeActivation) (scope : Nat) (parameter : Nat) (value : Value)
    (before after : ExecutionState)
    (bound : bindAll activation.act before.nextScope [(parameter, value)]
      (ownershipResultScopeState activation scope { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }) = .ok () after)
    : after.nextAct = before.nextAct + 1 ∧ after.nextScope = before.nextScope + 1 := by
  let scopeState := ownershipResultScopeState activation scope { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }
  cases step : bindRoot (.local activation.act before.nextScope parameter) value scopeState with
  | stop reason state | escape reason carriers state | jump target kind state =>
    simp [bindAll, List.forIn_cons, bind, pure, scopeState, step] at bound
  | ok result state =>
    cases result
    have same : state = after := by simpa [bindAll, List.forIn_cons, bind, pure, scopeState, step] using bound
    subst state
    have counters := bindRoot_counters _ value scopeState after step
    simpa [scopeState, ownershipResultScopeState] using counters

#print axioms bindAll_single_counters
#print axioms bindAll_single_outside
end Goose.Proofs.ConstructionAcceptedExecution
