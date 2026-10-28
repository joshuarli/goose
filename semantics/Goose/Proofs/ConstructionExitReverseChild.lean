import Goose.Proofs.ConstructionExecutionOwnershipLinkAllocation
import Goose.Proofs.ConstructionExecutionOwnershipCleanup
import Goose.Proofs.ConstructionExitFrameRelease

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership

def ActiveChildHasActiveParent (state : ConstructionState) : Prop :=
  ∀ (id : Nat) (row : PendingDestination) (parent : Nat), state.destinations[id]? = some row → row.use = .child parent →
    activeRow row = true → ∃ owner, state.destinations[parent]? = some owner ∧ activeRow owner = true

theorem initial_activeChildHasActiveParent : ActiveChildHasActiveParent .initial := by
  intro id row parent present
  simp [ConstructionState.initial] at present

theorem releaseExitReservation_activeChildHasActiveParent (state final : ConstructionState)
    (token : ExitReservationId) (valid : ActiveChildHasActiveParent state)
    (released : releaseExitReservation token state = .ok () final) :
    ActiveChildHasActiveParent final := by
  simp only [releaseExitReservation, ConstructionM.get, bind] at released
  cases ticket : state.exitReservations[token]? with
  | none => simp [ticket, ConstructionM.fail] at released
  | some status =>
    cases status <;> simp [ticket, ConstructionM.set, ConstructionM.fail, pure, bind] at released <;> subst final <;> exact valid

theorem openChild_new_child_parent_active (state final : ConstructionState) (parentId child : DestinationId)
    (ty : Goose.Construct.Ty) (layout : ReceivingLayout)
    (executed : openChild parentId ty layout state = .ok child final) :
    ∃ parent descendant count, final.destinations[parentId]? = some parent ∧
      parent.progress = .suspended count child ∧ activeRow parent = true ∧
      final.destinations[child]? = some descendant ∧ descendant.use = .child parentId := by
  obtain ⟨parent, count, found, suspended, link⟩ := openChild_success_parentLink state final parentId child ty layout executed
  simp only [DestinationForwardLink, suspended] at link
  obtain ⟨descendant, present, use, backing⟩ := link
  exact ⟨parent, descendant, count, found, suspended, by simp [activeRow, suspended], present, use⟩

theorem openExitReplacement_new_parent_active (state final : ConstructionState)
    (parentId replacement : DestinationId)
    (executed : openExitReplacement parentId state = .ok replacement final) :
    ∃ parent descendant count, final.destinations[parentId]? = some parent ∧
      parent.progress = .exiting count replacement ∧ activeRow parent = true ∧
      final.destinations[replacement]? = some descendant ∧ descendant.use = .replacement parentId := by
  obtain ⟨parent, count, found, exiting, link⟩ := openExitReplacement_success_parentLink state final parentId replacement executed
  simp only [DestinationForwardLink, exiting] at link
  obtain ⟨descendant, present, use, backing⟩ := link
  exact ⟨parent, descendant, count, found, exiting, by simp [activeRow, exiting], present, use⟩

#print axioms openExitReplacement_new_parent_active
#print axioms initial_activeChildHasActiveParent
#print axioms releaseExitReservation_activeChildHasActiveParent
#print axioms openChild_new_child_parent_active

end Goose.Proofs.ConstructionAcceptedExecution
