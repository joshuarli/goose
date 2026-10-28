import Goose.Proofs.ConstructionExitBlockedOpenChild

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

def ActiveChildUnique (state : ConstructionState) : Prop :=
  ∀ (parent first second : Nat) (left right : PendingDestination),
    state.destinations[first]? = some left → left.use = .child parent → activeRow left = true →
    state.destinations[second]? = some right → right.use = .child parent → activeRow right = true →
    first = second

theorem initial_activeChildUnique : ActiveChildUnique .initial := by
  intro parent first second left right present
  simp [ConstructionState.initial] at present

theorem releaseExitReservation_activeChildUnique (state final : ConstructionState)
    (token : ExitReservationId) (valid : ActiveChildUnique state)
    (released : releaseExitReservation token state = .ok () final) : ActiveChildUnique final := by
  simp only [releaseExitReservation, ConstructionM.get, bind] at released
  cases ticket : state.exitReservations[token]? with
  | none => simp [ticket, ConstructionM.fail] at released
  | some status =>
    cases status <;> simp [ticket, ConstructionM.set, ConstructionM.fail, pure, bind] at released <;> subst final <;> exact valid

theorem open_replacement_preserves_unique_children (before after : ConstructionState)
    (incoming selected count : Nat) (receiver : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some receiver) (opened : receiver.progress = .open count)
    (stored : before.storage[receiver.storage]? = some storage)
    (valid : ActiveChildUnique before)
    (executed : openExitReplacement incoming before = .ok selected after) : ActiveChildUnique after := by
  have frame := open_replacement_other_rows before after incoming selected count receiver storage present opened stored executed
  have fresh := open_replacement_fresh before after incoming selected count receiver storage present opened stored executed
  have parent := open_replacement_parent_exact before after incoming selected count receiver present opened executed
  obtain ⟨newParent, replacement, n, newParentFound, newParentPhase, newParentActive, replacementFound, replacementUse⟩ :=
    openExitReplacement_new_parent_active before after incoming selected executed
  have recover : ∀ (id : Nat) (row : PendingDestination) (owner : Nat), after.destinations[id]? = some row → row.use = .child owner → activeRow row = true →
      ∃ original, before.destinations[id]? = some original ∧ original.use = .child owner ∧ activeRow original = true := by
    intro id row owner found use active
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    rw [frame.1] at inside
    have old : id < before.destinations.size := by
      by_cases distinct : id = selected
      · subst id
        have same := Option.some.inj (replacementFound.symm.trans found)
        subst row
        rw [replacementUse] at use
        cases use
      · rw [fresh] at distinct
        exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp inside) distinct
    by_cases same : id = incoming
    · subst id
      have equal := Option.some.inj (parent.symm.trans found)
      subst row
      exact ⟨receiver, present, by simpa only using use, by simp [activeRow, opened]⟩
    · exact ⟨row, by rw [← frame.2 id same old]; exact found, use, active⟩
  intro owner first second left right leftFound leftUse leftActive rightFound rightUse rightActive
  obtain ⟨oldLeft, leftBefore, leftChild, leftWasActive⟩ := recover first left owner leftFound leftUse leftActive
  obtain ⟨oldRight, rightBefore, rightChild, rightWasActive⟩ := recover second right owner rightFound rightUse rightActive
  exact valid owner first second oldLeft oldRight leftBefore leftChild leftWasActive rightBefore rightChild rightWasActive

theorem reserve_open_preserves_unique_children (before after : ConstructionState)
    (incoming selected token count : Nat) (receiver : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some receiver) (opened : receiver.progress = .open (count + 1))
    (stored : before.storage[receiver.storage]? = some storage) (current : destinationCurrent before incoming = .ok incoming)
    (valid : ActiveChildUnique before)
    (reserved : reserveExitDestination incoming .newValue before = .ok (token, selected) after) : ActiveChildUnique after := by
  have renewal : renewReceivingDestination incoming before = .ok incoming before := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  have frontier : exitFrontierAction (before.destinations.size + 1) incoming before = .ok incoming before :=
    exitFrontier_open before.destinations.size incoming (count + 1) before receiver present opened
  rw [reserveExitDestination_equation] at reserved
  simp only [show (ExitSource.newValue == ExitSource.namedResult) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, renewal, bind, ConstructionM.get, frontier,
    reserveLookupStep, lookupDestination_result, present, opened, Bool.false_or] at reserved
  cases replacement : openExitReplacement incoming before with
  | fault reason state => simp only [replacement] at reserved; cases reserved
  | ok picked state =>
    simp only [replacement, ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.ok.injEq] at reserved
    obtain ⟨samePair, rfl⟩ := reserved
    cases samePair
    exact open_replacement_preserves_unique_children before state incoming selected (count + 1) receiver storage present opened stored valid replacement

theorem openChild_preserves_unique_children (before after : ConstructionState)
    (incoming selected count : Nat) (receiver : PendingDestination) (storage : ReceivingStorage)
    (ty : Goose.Construct.Ty) (layout : ReceivingLayout)
    (present : before.destinations[incoming]? = some receiver) (opened : receiver.progress = .open count)
    (stored : before.storage[receiver.storage]? = some storage)
    (blocked : ActiveChildParentBlocked before) (valid : ActiveChildUnique before)
    (executed : openChild incoming ty layout before = .ok selected after) : ActiveChildUnique after := by
  have frame := openChild_old_rows before after incoming selected count receiver storage ty layout present opened stored executed
  have fresh := frame.1
  have parent := frame.2.2.1
  obtain ⟨newParent, newChild, n, newParentFound, newParentPhase, newParentActive, childFound, childUse⟩ :=
    openChild_new_child_parent_active before after incoming selected ty layout executed
  have recover : ∀ (id : Nat) (row : PendingDestination) (owner : Nat), id ≠ selected →
      after.destinations[id]? = some row → row.use = .child owner → activeRow row = true →
      ∃ original, before.destinations[id]? = some original ∧ original.use = .child owner ∧ activeRow original = true := by
    intro id row owner distinct found use active
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    rw [frame.2.1] at inside
    have old : id < before.destinations.size := by
      rw [fresh] at distinct
      exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp inside) distinct
    by_cases same : id = incoming
    · subst id
      have equal := Option.some.inj (parent.symm.trans found)
      subst row
      exact ⟨receiver, present, by simpa only using use, by simp [activeRow, opened]⟩
    · exact ⟨row, by rw [← frame.2.2.2 id same old]; exact found, use, active⟩
  have noPrior : ∀ (id : Nat) (row : PendingDestination), before.destinations[id]? = some row → row.use = .child incoming → activeRow row = true → False := by
    intro id row rowPresent rowUse rowActive
    have inactive := activeChildParentBlocked_open_excludes_direct_child before blocked incoming id count receiver row present opened rowPresent rowUse
    rw [rowActive] at inactive
    cases inactive
  intro owner first second left right leftFound leftUse leftActive rightFound rightUse rightActive
  by_cases firstNew : first = selected
  · subst first
    have same := Option.some.inj (childFound.symm.trans leftFound)
    subst left
    have ownerEq := DestinationUse.child.inj (leftUse.symm.trans childUse)
    subst owner
    by_cases secondNew : second = selected
    · exact secondNew.symm
    · obtain ⟨old, oldFound, oldUse, oldActive⟩ := recover second right incoming secondNew rightFound rightUse rightActive
      exact False.elim (noPrior second old oldFound oldUse oldActive)
  · by_cases secondNew : second = selected
    · subst second
      have same := Option.some.inj (childFound.symm.trans rightFound)
      subst right
      have ownerEq := DestinationUse.child.inj (rightUse.symm.trans childUse)
      subst owner
      obtain ⟨old, oldFound, oldUse, oldActive⟩ := recover first left incoming firstNew leftFound leftUse leftActive
      exact False.elim (noPrior first old oldFound oldUse oldActive)
    · obtain ⟨oldLeft, leftBefore, leftChild, leftWasActive⟩ := recover first left owner firstNew leftFound leftUse leftActive
      obtain ⟨oldRight, rightBefore, rightChild, rightWasActive⟩ := recover second right owner secondNew rightFound rightUse rightActive
      exact valid owner first second oldLeft oldRight leftBefore leftChild leftWasActive rightBefore rightChild rightWasActive

#print axioms openChild_preserves_unique_children
#print axioms initial_activeChildUnique
#print axioms releaseExitReservation_activeChildUnique
#print axioms open_replacement_preserves_unique_children
#print axioms reserve_open_preserves_unique_children

end Goose.Proofs.ConstructionAcceptedExecution
