import Goose.Proofs.ConstructionExitReverseChild

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership

def ActiveChildParentBlocked (state : ConstructionState) : Prop :=
  ∀ (id : Nat) (row : PendingDestination) (parent : Nat),
    state.destinations[id]? = some row → row.use = .child parent → activeRow row = true →
    ∃ owner, state.destinations[parent]? = some owner ∧
      ((∃ count child, owner.progress = .suspended count child) ∨
        ∃ count replacement, owner.progress = .exiting count replacement)

theorem initial_activeChildParentBlocked : ActiveChildParentBlocked .initial := by
  intro id row parent present
  simp [ConstructionState.initial] at present

theorem releaseExitReservation_activeChildParentBlocked (state final : ConstructionState)
    (token : ExitReservationId) (valid : ActiveChildParentBlocked state)
    (released : releaseExitReservation token state = .ok () final) :
    ActiveChildParentBlocked final := by
  simp only [releaseExitReservation, ConstructionM.get, bind] at released
  cases ticket : state.exitReservations[token]? with
  | none => simp [ticket, ConstructionM.fail] at released
  | some status =>
    cases status <;> simp [ticket, ConstructionM.set, ConstructionM.fail, pure, bind] at released <;> subst final <;> exact valid

theorem activeChildParentBlocked_open_excludes_direct_child (state : ConstructionState)
    (valid : ActiveChildParentBlocked state) (parentId id count : Nat) (parent row : PendingDestination)
    (parentPresent : state.destinations[parentId]? = some parent) (opened : parent.progress = .open count)
    (present : state.destinations[id]? = some row) (child : row.use = .child parentId) :
    activeRow row = false := by
  cases active : activeRow row with
  | false => rfl
  | true =>
    have blocked := valid id row parentId present child active
    obtain ⟨owner, ownerFound, blocked⟩ := blocked
    have same := Option.some.inj (parentPresent.symm.trans ownerFound)
    subst owner
    rcases blocked with ⟨n, childId, progress⟩ | ⟨n, replacement, progress⟩ <;> rw [opened] at progress <;> cases progress

theorem openChild_new_parent_blocked (state final : ConstructionState) (parentId child : DestinationId)
    (ty : Goose.Construct.Ty) (layout : ReceivingLayout)
    (executed : openChild parentId ty layout state = .ok child final) :
    ∃ parent descendant count, final.destinations[parentId]? = some parent ∧
      parent.progress = .suspended count child ∧
      final.destinations[child]? = some descendant ∧ descendant.use = .child parentId := by
  obtain ⟨parent, descendant, count, found, suspended, active, present, use⟩ :=
    openChild_new_child_parent_active state final parentId child ty layout executed
  exact ⟨parent, descendant, count, found, suspended, present, use⟩

#print axioms initial_activeChildParentBlocked
#print axioms releaseExitReservation_activeChildParentBlocked
#print axioms activeChildParentBlocked_open_excludes_direct_child
#print axioms openChild_new_parent_blocked

end Goose.Proofs.ConstructionAcceptedExecution
