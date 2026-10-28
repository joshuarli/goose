import Goose.Proofs.ConstructionExitProtectedChildClosure
import Goose.Proofs.ConstructionExitChildWrite
import Goose.Proofs.ExitExecutionCompletedLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem child_invariants_replace_nonchild (before after : ConstructionState) (id : Nat)
    (old new : PendingDestination) (present : before.destinations[id]? = some old)
    (rows : after.destinations = before.destinations.set! id new)
    (newNonchild : ∀ owner, new.use ≠ .child owner)
    (samePhase : ChildParentPhase new ↔ ChildParentPhase old)
    (unique : ActiveChildUnique before) (blocked : ActiveChildParentBlocked before) :
    ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have current : after.destinations[id]? = some new := by
    rw [rows]
    simp [Array.set!_eq_setIfInBounds, inside]
  have outside : ∀ other, other ≠ id → after.destinations[other]? = before.destinations[other]? := by
    intro other distinct
    rw [rows]
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm distinct]
  have recover : ∀ (index : Nat) (row : PendingDestination) (parent : Nat),
      after.destinations[index]? = some row → row.use = .child parent → activeRow row = true →
      before.destinations[index]? = some row := by
    intro index row parent found use active
    by_cases same : index = id
    · subst index
      have equal := Option.some.inj (current.symm.trans found)
      subst row
      exact False.elim (newNonchild parent use)
    · simpa only [outside index same] using found
  constructor
  · intro owner first second left right leftFound leftUse leftActive rightFound rightUse rightActive
    exact unique owner first second left right (recover first left owner leftFound leftUse leftActive) leftUse leftActive
      (recover second right owner rightFound rightUse rightActive) rightUse rightActive
  · intro index row owner found use active
    have oldFound := recover index row owner found use active
    obtain ⟨oldOwner, oldOwnerFound, oldPhase⟩ := blocked index row owner oldFound use active
    by_cases same : owner = id
    · subst owner
      have equal := Option.some.inj (present.symm.trans oldOwnerFound)
      subst oldOwner
      exact ⟨new, current, samePhase.mpr oldPhase⟩
    · exact ⟨oldOwner, by rw [outside owner same]; exact oldOwnerFound, oldPhase⟩

theorem completed_receiver_landing_child_invariants (state : ConstructionState)
    (id old count : Nat) (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (indexed : DestinationCapabilitiesIndexed state) (ordered : DestinationOwnersOrdered state)
    (unique : ActiveChildUnique state) (blocked : ActiveChildParentBlocked state)
    (checked : ∃ rows, protectedExitDiscarded state old id = .ok rows)
    (present : state.destinations[id]? = some replacement)
    (replacementBuilt : replacement.progress = .built count) (receiverUse : superseded.use = .receiver) :
    ActiveChildUnique (completedLandingState state id old count replacement superseded storage none) ∧
      ActiveChildParentBlocked (completedLandingState state id old count replacement superseded storage none) := by
  let cleaned := abandonRowsState (protectedRows state old id) state
  have cleanup := abandonPreservingExit_exact state old id indexed checked
  have cleanUnique : ActiveChildUnique cleaned :=
    abandonPreservingExit_preserves_unique_children state cleaned old id indexed unique cleanup
  have cleanBlocked : ActiveChildParentBlocked cleaned :=
    abandonPreservingExit_preserves_blocked_children state cleaned old id indexed ordered blocked cleanup
  have cleanPresent : cleaned.destinations[id]? = some replacement := by
    have unchanged := abandonPreservingExit_replacement_untouched state old id indexed checked
    rw [cleanup] at unchanged
    simpa only [ConstructionResult.finalState] using unchanged.trans present
  apply child_invariants_replace_nonchild cleaned _ id replacement (landedReplacementRow replacement superseded count)
    cleanPresent _ _ _ cleanUnique cleanBlocked
  · simp only [completedLandingState]
    split <;> rfl
  · intro owner equal
    simp only [landedReplacementRow, receiverUse] at equal
    cases equal
  · simp [ChildParentPhase, replacementBuilt, landedReplacementRow]

theorem completed_receiver_step_child_invariants (state : ConstructionState)
    (id old count : Nat) (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (indexed : DestinationCapabilitiesIndexed state) (ordered : DestinationOwnersOrdered state)
    (unique : ActiveChildUnique state) (blocked : ActiveChildParentBlocked state)
    (checked : ∃ rows, protectedExitDiscarded state old id = .ok rows)
    (present : state.destinations[id]? = some replacement)
    (stored : state.storage[replacement.storage]? = some storage)
    (startOrder : superseded.capability.start ≤ replacement.capability.start)
    (inside : replacement.capability.start ≤ storage.bytes.size)
    (replacementBuilt : replacement.progress = .built count) (receiverUse : superseded.use = .receiver) :
    ∃ after, completedStep id old count replacement superseded none state = .ok () after ∧
      ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  refine ⟨completedLandingState state id old count replacement superseded storage none, ?_, ?_⟩
  · exact completedStep_success state id old count replacement superseded storage none indexed present stored
      startOrder inside (by intro parentId row impossible; cases impossible)
  · exact completed_receiver_landing_child_invariants state id old count replacement superseded storage
      indexed ordered unique blocked checked present replacementBuilt receiverUse

#print axioms completed_receiver_step_child_invariants
#print axioms child_invariants_replace_nonchild
#print axioms completed_receiver_landing_child_invariants

end Goose.Proofs.ConstructionAcceptedExecution
