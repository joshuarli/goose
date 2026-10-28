import Goose.Proofs.ConstructionExitChildWrite
import Goose.Proofs.ConstructionExitByteReservationStorage

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership

theorem open_replacement_suspended_frame (before after : ConstructionState)
    (incoming selected count child : Nat) (receiver : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some receiver) (suspended : receiver.progress = .suspended count child)
    (stored : before.storage[receiver.storage]? = some storage)
    (executed : openExitReplacement incoming before = .ok selected after) :
    selected = before.destinations.size ∧ after.destinations.size = before.destinations.size + 1 ∧
    after.destinations[incoming]? = some { receiver with progress := .exiting count selected } ∧
    ∀ other, other ≠ incoming → other < before.destinations.size →
      after.destinations[other]? = before.destinations[other]? := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [openExitReplacement, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite before incoming with
  | false => simp [allowed] at executed
  | true =>
    simp only [allowed, suspended, pure, bind, lookupStorage_result, stored, ConstructionM.get,
      ConstructionM.set, replaceDestination_result, replaceStorage_result, emit_result,
      Array.size_push, Nat.lt_succ_of_lt inside, storageInside, Array.size_setIfInBounds, ↓reduceIte] at executed
    split at executed <;>
      simp only [Nat.lt_succ_of_lt inside, storageInside, ↓reduceIte, bind, pure] at executed <;>
      cases executed <;>
      simp only [Array.size_set!, Array.size_push, true_and] <;>
      constructor
    all_goals try simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self,
      Nat.lt_succ_of_lt inside]
    all_goals
      intro other distinct bound
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne,
        Ne.symm distinct, Array.getElem?_push, Nat.ne_of_lt bound]

theorem open_suspended_replacement_preserves_blocked_children (before after : ConstructionState)
    (incoming selected count child : Nat) (receiver : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some receiver) (suspended : receiver.progress = .suspended count child)
    (stored : before.storage[receiver.storage]? = some storage)
    (ordered : DestinationOwnersOrdered before) (valid : ActiveChildParentBlocked before)
    (executed : openExitReplacement incoming before = .ok selected after) :
    ActiveChildParentBlocked after := by
  have frame := open_replacement_suspended_frame before after incoming selected count child receiver storage present suspended stored executed
  have fresh := frame.1
  have parent := frame.2.2.1
  obtain ⟨newParent, replacement, n, newParentFound, newParentPhase, newParentActive, replacementFound, replacementUse⟩ :=
    openExitReplacement_new_parent_active before after incoming selected executed
  have selectedRole : ∀ row, after.destinations[selected]? = some row → row.use = .replacement incoming := by
    intro row found
    have same := Option.some.inj (replacementFound.symm.trans found)
    subst row
    exact replacementUse
  have incomingInside := (Array.getElem?_eq_some_iff.mp present).1
  intro id row owner found use active
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  rw [frame.2.1] at inside
  have idOld : id < before.destinations.size := by
    by_cases old : id < before.destinations.size
    · exact old
    · have same : id = selected := by rw [fresh]; omega
      subst id
      have role := selectedRole row found
      rw [use] at role
      cases role
  have parentOld : owner < id := by
    by_cases eq : id = incoming
    · subst id
      have same := Option.some.inj (parent.symm.trans found)
      subst row
      have oldUse : receiver.use = .child owner := by simpa only using use
      simpa only [oldUse] using ordered incoming receiver present
    · have beforeFound : before.destinations[id]? = some row := by
        rw [← frame.2.2.2 id eq idOld]
        exact found
      simpa only [use] using ordered id row beforeFound
  have oldFound : ∃ oldRow, before.destinations[id]? = some oldRow ∧
      oldRow.use = .child owner ∧ activeRow oldRow = true := by
    by_cases eq : id = incoming
    · subst id
      have same := Option.some.inj (parent.symm.trans found)
      subst row
      refine ⟨receiver, present, ?_, ?_⟩
      · simpa only using use
      · simp [activeRow, suspended]
    · refine ⟨row, ?_, use, active⟩
      rw [← frame.2.2.2 id eq idOld]
      exact found
  obtain ⟨oldRow, oldPresent, oldUse, oldActive⟩ := oldFound
  obtain ⟨oldOwner, ownerFound, blocked⟩ := valid id oldRow owner oldPresent oldUse oldActive
  by_cases ownerIsIncoming : owner = incoming
  · subst owner
    refine ⟨{ receiver with progress := .exiting count selected }, parent, ?_⟩
    exact Or.inr ⟨count, selected, rfl⟩
  · have ownerInside : owner < before.destinations.size := Nat.lt_trans parentOld idOld
    have afterFound : after.destinations[owner]? = some oldOwner := by
      rw [frame.2.2.2 owner ownerIsIncoming ownerInside]
      exact ownerFound
    exact ⟨oldOwner, afterFound, blocked⟩

theorem open_suspended_replacement_preserves_unique_children (before after : ConstructionState)
    (incoming selected count child : Nat) (receiver : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some receiver) (suspended : receiver.progress = .suspended count child)
    (stored : before.storage[receiver.storage]? = some storage)
    (valid : ActiveChildUnique before)
    (executed : openExitReplacement incoming before = .ok selected after) : ActiveChildUnique after := by
  have frame := open_replacement_suspended_frame before after incoming selected count child receiver storage present suspended stored executed
  have fresh := frame.1
  have parent := frame.2.2.1
  obtain ⟨newParent, replacement, n, newParentFound, newParentPhase, newParentActive, replacementFound, replacementUse⟩ :=
    openExitReplacement_new_parent_active before after incoming selected executed
  have recover : ∀ (id : Nat) (row : PendingDestination) (owner : Nat), after.destinations[id]? = some row → row.use = .child owner → activeRow row = true →
      ∃ original, before.destinations[id]? = some original ∧ original.use = .child owner ∧ activeRow original = true := by
    intro id row owner found use active
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    rw [frame.2.1] at inside
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
      exact ⟨receiver, present, by simpa only using use, by simp [activeRow, suspended]⟩
    · exact ⟨row, by rw [← frame.2.2.2 id same old]; exact found, use, active⟩
  intro owner first second left right leftFound leftUse leftActive rightFound rightUse rightActive
  obtain ⟨oldLeft, leftBefore, leftChild, leftWasActive⟩ := recover first left owner leftFound leftUse leftActive
  obtain ⟨oldRight, rightBefore, rightChild, rightWasActive⟩ := recover second right owner rightFound rightUse rightActive
  exact valid owner first second oldLeft oldRight leftBefore leftChild leftWasActive rightBefore rightChild rightWasActive

#print axioms open_suspended_replacement_preserves_blocked_children
#print axioms open_suspended_replacement_preserves_unique_children
#print axioms open_replacement_suspended_frame

end Goose.Proofs.ConstructionAcceptedExecution
