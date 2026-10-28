import Goose.Proofs.ConstructionAcceptedScopeWorld
import Goose.Proofs.ConstructionAcceptedEarlierCallerFrame
import Goose.Proofs.ConstructionRootCorrespondenceWrites
import Goose.Proofs.ConstructionAcceptedBindings

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

def EarlierCallerObservations (frontier : Nat) (before after : ExecutionState) (types nextTypes : RootTypes) : Prop :=
  ∀ root, EarlierCallerRoot frontier root →
    after.objects.lookup root = before.objects.lookup root ∧
    after.objectOrdinals.lookup root = before.objectOrdinals.lookup root ∧ nextTypes root = types root

theorem EarlierCallerRoot.mono {first next : Nat} (bound : first ≤ next) (root : Goose.Core.RootInst)
    (earlier : EarlierCallerRoot first root) : EarlierCallerRoot next root := by
  cases root with
  | global id => trivial
  | «local» act scope id => exact Nat.lt_of_lt_of_le earlier bound

theorem EarlierCallerObservations.refl (frontier : Nat) (state : ExecutionState) (types : RootTypes) :
    EarlierCallerObservations frontier state state types types := by
  intro root earlier
  exact ⟨rfl, rfl, rfl⟩

theorem EarlierCallerObservations.restrict {frontier nextFrontier : Nat} {before after : ExecutionState}
    {types nextTypes : RootTypes} (bound : frontier ≤ nextFrontier)
    (observations : EarlierCallerObservations nextFrontier before after types nextTypes) :
    EarlierCallerObservations frontier before after types nextTypes := by
  intro root earlier
  exact observations root (earlier.mono bound root)

theorem EarlierCallerObservations.trans {frontier nextFrontier : Nat} {before middle after : ExecutionState}
    {types middleTypes finalTypes : RootTypes} (bound : frontier ≤ nextFrontier)
    (first : EarlierCallerObservations frontier before middle types middleTypes)
    (second : EarlierCallerObservations nextFrontier middle after middleTypes finalTypes) :
    EarlierCallerObservations frontier before after types finalTypes := by
  intro root earlier
  obtain ⟨firstObjects, firstOrdinals, firstTypes⟩ := first root earlier
  obtain ⟨secondObjects, secondOrdinals, secondTypes⟩ := second root (earlier.mono bound root)
  exact ⟨secondObjects.trans firstObjects, secondOrdinals.trans firstOrdinals, secondTypes.trans firstTypes⟩

theorem EarlierCallerObservations.bindFreshLocal (frontier act scope id : Nat) (ty : Ty) (value : Value)
    (before after : ExecutionState) (types : RootTypes) (bound : frontier ≤ act)
    (boundRoot : bindRoot (.local act scope id) value before = .ok () after) :
    EarlierCallerObservations frontier before after types (registerRootType types (.local act scope id) ty) := by
  intro root earlier
  have different : root ≠ .local act scope id := by
    intro same
    subst root
    exact (Nat.not_lt_of_ge bound) earlier
  exact ⟨bindRoot_lookup_other _ root value before after boundRoot different,
    bindRoot_ordinals_other _ root value before after boundRoot different,
    by simp [registerRootType, different]⟩

theorem EarlierCallerRoot.outsideScope {frontier : Nat} (activation : RuntimeActivation) (scope scopeInst : Nat)
    (bound : frontier ≤ activation.act) (root : Goose.Core.RootInst) (earlier : EarlierCallerRoot frontier root) :
    (Goose.Proofs.Exit.runtimeScopeRoots activation scope scopeInst).contains root = false := by
  apply Bool.eq_false_iff.mpr
  intro contains
  have member := List.contains_iff_mem.mp contains
  simp only [Goose.Proofs.Exit.runtimeScopeRoots, List.mem_filterMap] at member
  obtain ⟨entry, _, found⟩ := member
  split at found
  · have same : .local activation.act scopeInst entry.2 = root := Option.some.inj found
    rw [← same] at earlier
    exact (Nat.not_lt_of_ge bound) earlier
  · cases found

theorem EarlierCallerObservations.releaseScope (frontier : Nat) (activation : RuntimeActivation) (scope scopeInst : Nat)
    (state : ExecutionState) (types : RootTypes) (bound : frontier ≤ activation.act) :
    EarlierCallerObservations frontier state (releaseScopeState activation scope scopeInst state) types types := by
  intro root earlier
  have outside := earlier.outsideScope activation scope scopeInst bound root
  exact ⟨Goose.Proofs.ExitExecution.releaseScopeState_root_lookup activation scope scopeInst state root outside,
    releaseScopeState_ordinal_lookup activation scope scopeInst state root outside, rfl⟩

theorem EarlierCallerObservations.enterScope (frontier : Nat) (activation : RuntimeActivation) (scope : Nat)
    (state : ExecutionState) (types : RootTypes) :
    EarlierCallerObservations frontier state (ownershipResultScopeState activation scope state) types types := by
  intro root earlier
  exact ⟨rfl, rfl, rfl⟩

theorem EarlierCallerObservations.finishActivation (frontier : Nat) (activation : RuntimeActivation)
    (state : ExecutionState) (types : RootTypes) :
    EarlierCallerObservations frontier state
      { state with activations := state.activations.filter (fun current => current.act != activation.act) } types types := by
  intro root earlier
  exact ⟨rfl, rfl, rfl⟩

#print axioms EarlierCallerObservations.releaseScope
#print axioms EarlierCallerObservations.enterScope
#print axioms EarlierCallerObservations.finishActivation
theorem AcceptedFrame.afterEarlierObservations
    {config : EvalConfig} {accepted : AcceptedModule config} {frame : ConstructionSourceFrame}
    {before after : ExecutionState} {types nextTypes : RootTypes}
    (source : AcceptedFrame config accepted frame before types)
    (acts : before.nextAct ≤ after.nextAct) (scopes : before.nextScope ≤ after.nextScope)
    (observations : EarlierCallerObservations before.nextAct before after types nextTypes) :
    AcceptedFrame config accepted frame after nextTypes := by
  exact source.afterEarlierActivations acts scopes (fun root earlier => (observations root earlier).1)
    (fun root earlier => (observations root earlier).2.1) (fun root earlier => (observations root earlier).2.2)

#print axioms EarlierCallerObservations.bindFreshLocal
#print axioms EarlierCallerObservations.restrict
#print axioms EarlierCallerObservations.trans
#print axioms AcceptedFrame.afterEarlierObservations
end Goose.Proofs.ConstructionAcceptedExecution
