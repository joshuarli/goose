import Goose.Proofs.ConstructionExitUniqueChildren

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership

theorem attachChild_exact_rows (before after : ConstructionState) (parentId childId count childCount : Nat)
    (parent child : PendingDestination)
    (parentFound : before.destinations[parentId]? = some parent)
    (childFound : before.destinations[childId]? = some child)
    (parentPhase : parent.progress = .suspended count childId)
    (childPhase : child.progress = .built childCount) (childUse : child.use = .child parentId)
    (executed : attachChild parentId childId before = .ok () after) :
    after.destinations = (before.destinations.set! childId { child with progress := .attached childCount }).set!
      parentId { parent with progress := .open (count + 1), writeEnd := child.writeEnd } := by
  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).1
  have childInside := (Array.getElem?_eq_some_iff.mp childFound).1
  simp only [attachChild, writableDestination_result, parentFound, childFound, bind] at executed
  cases parentAllowed : destinationCanWrite before parentId with
  | false => simp [parentAllowed] at executed
  | true =>
    simp only [parentAllowed, childFound, bind] at executed
    cases childAllowed : destinationCanWrite before childId with
    | false => simp [childAllowed] at executed
    | true =>
      simp only [childAllowed, parentPhase, childPhase, childUse, bind] at executed
      split at executed
      · contradiction
      · split at executed
        · contradiction
        · simp only [replaceDestination_result, childInside, parentInside, Array.size_set!, ↓reduceIte,
            emit_result, bind, pure, ConstructionResult.ok.injEq, true_and] at executed
          subst after
          simp only [childUse, parentPhase]

theorem attachChild_preserves_unique_children (before after : ConstructionState) (parentId childId count childCount : Nat)
    (parent child : PendingDestination)
    (parentFound : before.destinations[parentId]? = some parent)
    (childFound : before.destinations[childId]? = some child)
    (parentPhase : parent.progress = .suspended count childId)
    (childPhase : child.progress = .built childCount) (childUse : child.use = .child parentId)
    (ordered : DestinationOwnersOrdered before) (valid : ActiveChildUnique before)
    (executed : attachChild parentId childId before = .ok () after) : ActiveChildUnique after := by
  have rows := attachChild_exact_rows before after parentId childId count childCount parent child parentFound childFound parentPhase childPhase childUse executed
  have earlier : parentId < childId := by simpa only [childUse] using ordered childId child childFound
  have distinct : childId ≠ parentId := Nat.ne_of_gt earlier
  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).1
  have childInside := (Array.getElem?_eq_some_iff.mp childFound).1
  have parentAfter : after.destinations[parentId]? = some { parent with progress := .open (count + 1), writeEnd := child.writeEnd } := by
    rw [rows]
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self, parentInside]
  have childAfter : after.destinations[childId]? = some { child with progress := .attached childCount } := by
    rw [rows]
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Array.getElem?_setIfInBounds_self,
      Ne.symm distinct, childInside]
  have recover : ∀ (id : Nat) (row : PendingDestination) (owner : Nat),
      after.destinations[id]? = some row → row.use = .child owner → activeRow row = true →
      ∃ original, before.destinations[id]? = some original ∧ original.use = .child owner ∧ activeRow original = true := by
    intro id row owner found use active
    by_cases isParent : id = parentId
    · subst id
      have same := Option.some.inj (parentAfter.symm.trans found)
      subst row
      exact ⟨parent, parentFound, by simpa only using use, by simp [activeRow, parentPhase]⟩
    · by_cases isChild : id = childId
      · subst id
        have same := Option.some.inj (childAfter.symm.trans found)
        subst row
        simp [activeRow] at active
      · have same : after.destinations[id]? = before.destinations[id]? := by
          rw [rows]
          simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm isParent, Ne.symm isChild]
        exact ⟨row, by rw [← same]; exact found, use, active⟩
  intro owner first second left right leftFound leftUse leftActive rightFound rightUse rightActive
  obtain ⟨oldLeft, leftBefore, leftChild, leftWasActive⟩ := recover first left owner leftFound leftUse leftActive
  obtain ⟨oldRight, rightBefore, rightChild, rightWasActive⟩ := recover second right owner rightFound rightUse rightActive
  exact valid owner first second oldLeft oldRight leftBefore leftChild leftWasActive rightBefore rightChild rightWasActive

theorem attachChild_preserves_blocked_children (before after : ConstructionState) (parentId childId count childCount : Nat)
    (parent child : PendingDestination)
    (parentFound : before.destinations[parentId]? = some parent)
    (childFound : before.destinations[childId]? = some child)
    (parentPhase : parent.progress = .suspended count childId)
    (childPhase : child.progress = .built childCount) (childUse : child.use = .child parentId)
    (ordered : DestinationOwnersOrdered before) (unique : ActiveChildUnique before)
    (valid : ActiveChildParentBlocked before)
    (executed : attachChild parentId childId before = .ok () after) : ActiveChildParentBlocked after := by
  have rows := attachChild_exact_rows before after parentId childId count childCount parent child parentFound childFound parentPhase childPhase childUse executed
  have earlier : parentId < childId := by simpa only [childUse] using ordered childId child childFound
  have distinct : childId ≠ parentId := Nat.ne_of_gt earlier
  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).1
  have childInside := (Array.getElem?_eq_some_iff.mp childFound).1
  have parentAfter : after.destinations[parentId]? = some { parent with progress := .open (count + 1), writeEnd := child.writeEnd } := by
    rw [rows]
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self, parentInside]
  have childAfter : after.destinations[childId]? = some { child with progress := .attached childCount } := by
    rw [rows]
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Array.getElem?_setIfInBounds_self,
      Ne.symm distinct, childInside]
  have recover : ∀ (id : Nat) (row : PendingDestination) (owner : Nat),
      after.destinations[id]? = some row → row.use = .child owner → activeRow row = true →
      ∃ original, before.destinations[id]? = some original ∧ original.use = .child owner ∧ activeRow original = true := by
    intro id row owner found use active
    by_cases isParent : id = parentId
    · subst id
      have same := Option.some.inj (parentAfter.symm.trans found)
      subst row
      exact ⟨parent, parentFound, by simpa only using use, by simp [activeRow, parentPhase]⟩
    · by_cases isChild : id = childId
      · subst id
        have same := Option.some.inj (childAfter.symm.trans found)
        subst row
        simp [activeRow] at active
      · have same : after.destinations[id]? = before.destinations[id]? := by
          rw [rows]
          simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm isParent, Ne.symm isChild]
        exact ⟨row, by rw [← same]; exact found, use, active⟩
  intro id row owner found use active
  obtain ⟨original, originalFound, originalUse, originalActive⟩ := recover id row owner found use active
  obtain ⟨oldOwner, oldOwnerFound, oldBlocked⟩ := valid id original owner originalFound originalUse originalActive
  have ownerNotParent : owner ≠ parentId := by
    intro equal
    subst owner
    have sameId := unique parentId id childId original child originalFound originalUse originalActive
      childFound childUse (by simp [activeRow, childPhase])
    subst id
    have same := Option.some.inj (childAfter.symm.trans found)
    subst row
    simp [activeRow] at active
  have ownerNotChild : owner ≠ childId := by
    intro equal
    subst owner
    have same := Option.some.inj (childFound.symm.trans oldOwnerFound)
    subst oldOwner
    rcases oldBlocked with ⟨n, target, phase⟩ | ⟨n, target, phase⟩ <;> rw [childPhase] at phase <;> cases phase
  have sameOwner : after.destinations[owner]? = before.destinations[owner]? := by
    rw [rows]
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm ownerNotParent, Ne.symm ownerNotChild]
  exact ⟨oldOwner, by rw [sameOwner]; exact oldOwnerFound, oldBlocked⟩

theorem attachChild_preserves_child_invariants (before after : ConstructionState) (parentId childId count childCount : Nat)
    (parent child : PendingDestination)
    (parentFound : before.destinations[parentId]? = some parent)
    (childFound : before.destinations[childId]? = some child)
    (parentPhase : parent.progress = .suspended count childId)
    (childPhase : child.progress = .built childCount) (childUse : child.use = .child parentId)
    (ordered : DestinationOwnersOrdered before) (unique : ActiveChildUnique before)
    (blocked : ActiveChildParentBlocked before)
    (executed : attachChild parentId childId before = .ok () after) :
    ActiveChildUnique after ∧ ActiveChildParentBlocked after :=
  ⟨attachChild_preserves_unique_children before after parentId childId count childCount parent child parentFound childFound
    parentPhase childPhase childUse ordered unique executed,
   attachChild_preserves_blocked_children before after parentId childId count childCount parent child parentFound childFound
    parentPhase childPhase childUse ordered unique blocked executed⟩

#print axioms attachChild_preserves_child_invariants
#print axioms attachChild_preserves_blocked_children
#print axioms attachChild_preserves_unique_children
#print axioms attachChild_exact_rows

end Goose.Proofs.ConstructionAcceptedExecution
