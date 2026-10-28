import Goose.Proofs.ConstructionAcceptedEarlierCallerFrame
import Goose.Proofs.ConstructionRootCorrespondenceWrites
import Goose.Proofs.ConstructionAcceptedBindings

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

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
#print axioms EarlierCallerObservations.trans
#print axioms AcceptedFrame.afterEarlierObservations
end Goose.Proofs.ConstructionAcceptedExecution
