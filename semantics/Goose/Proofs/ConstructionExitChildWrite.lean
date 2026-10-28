import Goose.Proofs.ConstructionExitAttachFrame
import Goose.Proofs.ConstructionElementWriteTransition

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionStorage

def ChildParentPhase (row : PendingDestination) : Prop :=
  (∃ count child, row.progress = .suspended count child) ∨
    ∃ count replacement, row.progress = .exiting count replacement

theorem child_invariants_replace_progress (before after : ConstructionState) (id : Nat)
    (old new : PendingDestination) (present : before.destinations[id]? = some old)
    (rows : after.destinations = before.destinations.set! id new)
    (sameUse : new.use = old.use) (sameActive : activeRow new = activeRow old)
    (samePhase : ChildParentPhase new ↔ ChildParentPhase old)
    (unique : ActiveChildUnique before) (blocked : ActiveChildParentBlocked before) :
    ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have current : after.destinations[id]? = some new := by
    rw [rows]
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self, inside]
  have outside : ∀ other, other ≠ id → after.destinations[other]? = before.destinations[other]? := by
    intro other distinct
    rw [rows]
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm distinct]
  have recover : ∀ (index : Nat) (row : PendingDestination) (parent : Nat),
      after.destinations[index]? = some row → row.use = .child parent → activeRow row = true →
      ∃ previous, before.destinations[index]? = some previous ∧ previous.use = .child parent ∧ activeRow previous = true := by
    intro index row parent found use active
    by_cases same : index = id
    · subst index
      have equal := Option.some.inj (current.symm.trans found)
      subst row
      exact ⟨old, present, sameUse.symm.trans use, sameActive.symm.trans active⟩
    · exact ⟨row, by rw [← outside index same]; exact found, use, active⟩
  constructor
  · intro owner first second left right leftFound leftUse leftActive rightFound rightUse rightActive
    obtain ⟨oldLeft, leftBefore, leftChild, leftWasActive⟩ := recover first left owner leftFound leftUse leftActive
    obtain ⟨oldRight, rightBefore, rightChild, rightWasActive⟩ := recover second right owner rightFound rightUse rightActive
    exact unique owner first second oldLeft oldRight leftBefore leftChild leftWasActive rightBefore rightChild rightWasActive
  · intro index row owner found use active
    obtain ⟨previous, oldFound, oldUse, oldActive⟩ := recover index row owner found use active
    obtain ⟨oldOwner, oldOwnerFound, oldPhase⟩ := blocked index previous owner oldFound oldUse oldActive
    by_cases same : owner = id
    · subst owner
      have equal := Option.some.inj (present.symm.trans oldOwnerFound)
      subst oldOwner
      exact ⟨new, current, samePhase.mpr oldPhase⟩
    · exact ⟨oldOwner, by rw [outside owner same]; exact oldOwnerFound, oldPhase⟩

theorem writeElement_preserves_child_invariants (before after : ConstructionState)
    (id : Nat) (payload : ByteArray) (unique : ActiveChildUnique before)
    (blocked : ActiveChildParentBlocked before)
    (executed : writeElement id payload before = .ok () after) :
    ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  have transition := writeElement_transition id payload before
  rw [executed] at transition
  cases transition with
  | written row storage count present stored opened =>
    apply child_invariants_replace_progress before _ id row
      { row with progress := .open (count + 1), writeEnd := row.writeEnd + payload.size }
      present rfl rfl _ _ unique blocked
    · simp [activeRow, opened]
    · simp [ChildParentPhase, opened]

theorem finish_packed_preserves_child_invariants (before after : ConstructionState)
    (id count : Nat) (row : PendingDestination) (present : before.destinations[id]? = some row)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (request : row.capability.request = .value) (unique : ActiveChildUnique before)
    (blocked : ActiveChildParentBlocked before)
    (executed : finishDestination id before = .ok () after) :
    ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  simp only [finishDestination, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite before id with
  | false => simp [allowed] at executed
  | true =>
    simp only [allowed, opened, packed, hasPrefix_result, request, beq_self_eq_true,
      Bool.and_self, ↓reduceIte, lookupStorage_result, bind] at executed
    cases stored : before.storage[row.storage]? with
    | none => simp [stored] at executed
    | some storage =>
      have bound := (Array.getElem?_eq_some_iff.mp stored).1
      simp only [stored, replaceStorage_result, replaceDestination_result, bound, inside,
        bind, pure, ↓reduceIte] at executed
      cases executed
      apply child_invariants_replace_progress before _ id row { row with progress := .built count }
        present (by simp only [packed]) rfl _ _ unique blocked
      · simp [activeRow, opened]
      · simp [ChildParentPhase, opened]

#print axioms finish_packed_preserves_child_invariants
#print axioms child_invariants_replace_progress
#print axioms writeElement_preserves_child_invariants

end Goose.Proofs.ConstructionAcceptedExecution
