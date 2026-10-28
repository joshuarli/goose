import Goose.Proofs.ConstructionExitBlockedOpenReplacement

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership

theorem openChild_old_rows (before after : ConstructionState) (incoming selected count : Nat)
    (receiver : PendingDestination) (storage : ReceivingStorage) (ty : Goose.Construct.Ty) (layout : ReceivingLayout)
    (present : before.destinations[incoming]? = some receiver) (opened : receiver.progress = .open count)
    (stored : before.storage[receiver.storage]? = some storage)
    (executed : openChild incoming ty layout before = .ok selected after) :
    selected = before.destinations.size ∧ after.destinations.size = before.destinations.size + 1 ∧
    after.destinations[incoming]? = some { receiver with progress := .suspended count selected } ∧
    ∀ other, other ≠ incoming → other < before.destinations.size →
      after.destinations[other]? = before.destinations[other]? := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [openChild, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite before incoming with
  | false => simp [allowed] at executed
  | true =>
    simp only [allowed, opened, lookupStorage_result, stored, bind] at executed
    split at executed
    · contradiction
    · simp only [ConstructionM.get, ConstructionM.set, pure, bind,
        replaceDestination_result, replaceStorage_result, emit_result,
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

theorem openChild_preserves_blocked_children (before after : ConstructionState)
    (incoming selected count : Nat) (receiver : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some receiver) (opened : receiver.progress = .open count)
    (stored : before.storage[receiver.storage]? = some storage)
    (ty : Goose.Construct.Ty) (layout : ReceivingLayout)
    (ordered : DestinationOwnersOrdered before) (valid : ActiveChildParentBlocked before)
    (executed : openChild incoming ty layout before = .ok selected after) :
    ActiveChildParentBlocked after := by
  have frame := openChild_old_rows before after incoming selected count receiver storage ty layout present opened stored executed
  have fresh := frame.1
  have parent := frame.2.2.1
  obtain ⟨newParent, replacement, n, newParentFound, newParentPhase, newParentActive, replacementFound, replacementUse⟩ :=
    openChild_new_child_parent_active before after incoming selected ty layout executed
  have incomingInside := (Array.getElem?_eq_some_iff.mp present).1
  intro id row owner found use active
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  rw [frame.2.1] at inside
  by_cases new : id = selected
  · subst id
    have same := Option.some.inj (replacementFound.symm.trans found)
    subst row
    have ownerEq : owner = incoming := DestinationUse.child.inj (use.symm.trans replacementUse)
    subst owner
    exact ⟨newParent, newParentFound, Or.inl ⟨n, selected, newParentPhase⟩⟩
  have idOld : id < before.destinations.size := by
    rw [fresh] at new
    exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp inside) new
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
      · simp [activeRow, opened]
    · refine ⟨row, ?_, use, active⟩
      rw [← frame.2.2.2 id eq idOld]
      exact found
  obtain ⟨oldRow, oldPresent, oldUse, oldActive⟩ := oldFound
  obtain ⟨oldOwner, ownerFound, blocked⟩ := valid id oldRow owner oldPresent oldUse oldActive
  by_cases ownerIsIncoming : owner = incoming
  · subst owner
    refine ⟨{ receiver with progress := .suspended count selected }, parent, ?_⟩
    exact Or.inl ⟨count, selected, rfl⟩
  · have ownerInside : owner < before.destinations.size := Nat.lt_trans parentOld idOld
    have afterFound : after.destinations[owner]? = some oldOwner := by
      rw [frame.2.2.2 owner ownerIsIncoming ownerInside]
      exact ownerFound
    exact ⟨oldOwner, afterFound, blocked⟩

#print axioms openChild_preserves_blocked_children
#print axioms openChild_old_rows

end Goose.Proofs.ConstructionAcceptedExecution
