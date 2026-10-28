import Goose.Proofs.ConstructionExitLandingReceiverChildren
import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsLandingForward
import Goose.Proofs.ExitExecutionCommitLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem completed_replacement_landing_child_invariants (state : ConstructionState)
    (id old count parentId parentCount : Nat) (replacement superseded parent : PendingDestination) (storage : ReceivingStorage)
    (indexed : DestinationCapabilitiesIndexed state) (ordered : DestinationOwnersOrdered state)
    (unique : ActiveChildUnique state) (blocked : ActiveChildParentBlocked state)
    (checked : ∃ rows, protectedExitDiscarded state old id = .ok rows)
    (present : state.destinations[id]? = some replacement) (replacementBuilt : replacement.progress = .built count)
    (parentFound : state.destinations[parentId]? = some parent) (parentPhase : parent.progress = .exiting parentCount old)
    (anchorUse : superseded.use = .replacement parentId)
    (parentEarlier : parentId < old) (parentDifferent : parentId ≠ id) :
    ActiveChildUnique (completedLandingState state id old count replacement superseded storage
      (some (parentId, { parent with progress := .exiting parentCount id }))) ∧
      ActiveChildParentBlocked (completedLandingState state id old count replacement superseded storage
      (some (parentId, { parent with progress := .exiting parentCount id }))) := by
  let cleaned := abandonRowsState (protectedRows state old id) state
  let adopted := { cleaned with destinations := cleaned.destinations.set! id (landedReplacementRow replacement superseded count) }
  let reparented := { adopted with destinations := adopted.destinations.set! parentId { parent with progress := .exiting parentCount id } }
  have cleanup := abandonPreservingExit_exact state old id indexed checked
  have cleanUnique : ActiveChildUnique cleaned := abandonPreservingExit_preserves_unique_children state cleaned old id indexed unique cleanup
  have cleanBlocked : ActiveChildParentBlocked cleaned := abandonPreservingExit_preserves_blocked_children state cleaned old id indexed ordered blocked cleanup
  have cleanReplacement : cleaned.destinations[id]? = some replacement := by
    have unchanged := protectedCleanup_lookup_outside state old id id ordered (Or.inl rfl)
    exact unchanged.trans present
  have cleanParent : cleaned.destinations[parentId]? = some parent := by
    have unchanged := protectedCleanup_lookup_outside state old id parentId ordered (Or.inr parentEarlier)
    exact unchanged.trans parentFound
  have adoptedInvariants : ActiveChildUnique adopted ∧ ActiveChildParentBlocked adopted := by
    apply child_invariants_replace_nonchild cleaned adopted id replacement (landedReplacementRow replacement superseded count)
      cleanReplacement rfl _ _ cleanUnique cleanBlocked
    · intro owner equal
      simp only [landedReplacementRow, anchorUse] at equal
      cases equal
    · simp [ChildParentPhase, replacementBuilt, landedReplacementRow]
  have adoptedParent : adopted.destinations[parentId]? = some parent := by
    simpa [adopted, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm parentDifferent] using cleanParent
  have reparentedInvariants : ActiveChildUnique reparented ∧ ActiveChildParentBlocked reparented := by
    apply child_invariants_replace_progress adopted reparented parentId parent
      { parent with progress := .exiting parentCount id } adoptedParent rfl rfl _ _ adoptedInvariants.1 adoptedInvariants.2
    · simp [activeRow, parentPhase]
    · simp [ChildParentPhase, parentPhase]
  by_cases moving : superseded.capability.start < replacement.capability.start
  · simpa only [completedLandingState, moving, ↓reduceIte, ActiveChildUnique, ActiveChildParentBlocked, reparented, adopted] using reparentedInvariants
  · simpa only [completedLandingState, moving, ↓reduceIte, ActiveChildUnique, ActiveChildParentBlocked, reparented, adopted] using reparentedInvariants

theorem commit_replacement_landing_child_invariants (state : ConstructionState)
    (id old count parentId parentCount : Nat) (replacement anchor parent : PendingDestination)
    (storage : ReceivingStorage) (receiving : Option DestinationId) (chain : List DestinationId)
    (lifecycle : DestinationLifecycleInvariant state) (unique : ActiveChildUnique state)
    (blocked : ActiveChildParentBlocked state) (checked : ∃ rows, protectedExitDiscarded state old id = .ok rows)
    (present : state.destinations[id]? = some replacement) (built : replacement.progress = .built count)
    (stored : state.storage[replacement.storage]? = some storage)
    (selected : exitLandingAnchor (state.destinations.size + 1) id replacement.storage receiving state =
      .ok (old, anchor, chain) state)
    (anchorUse : anchor.use = .replacement parentId)
    (parentFound : state.destinations[parentId]? = some parent) (parentPhase : parent.progress = .exiting parentCount old)
    (startOrder : anchor.capability.start ≤ replacement.capability.start)
    (inside : replacement.capability.start ≤ storage.bytes.size) :
    ∃ after, commitExitReplacement receiving id state = .ok () after ∧
      ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  obtain ⟨_, anchorEarlier, anchorPresent⟩ := exitLandingAnchor_success _ _ _ _ state state old anchor chain selected
  have parentEarlier : parentId < old := by simpa only [anchorUse] using lifecycle.2.2.2 old anchor anchorPresent
  have parentDifferent : parentId ≠ id := Nat.ne_of_lt (Nat.lt_trans parentEarlier anchorEarlier)
  let update := some (parentId, { parent with progress := .exiting parentCount id })
  have bound : ∀ actualId actual, update = some (actualId, actual) → actualId < state.destinations.size := by
    intro actualId actual same
    have ids : parentId = actualId := congrArg Prod.fst (Option.some.inj same)
    rw [← ids]
    exact (Array.getElem?_eq_some_iff.mp parentFound).1
  have step := completedStep_success state id old count replacement anchor storage update lifecycle.2.1 present stored startOrder inside bound
  have executed : commitExitReplacement receiving id state = .ok ()
      (committedExitState state id old count replacement anchor storage update chain) := by
    simp only [commitExitReplacement, lookupDestination_result, present, built, ConstructionM.get,
      selected, anchorUse, parentFound, parentPhase, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      bind, pure]
    simp only [completedStep, update] at step
    rw [step]
    rfl
  refine ⟨_, executed, ?_⟩
  have candidates := completed_replacement_landing_child_invariants state id old count parentId parentCount
    replacement anchor parent storage lifecycle.2.1 lifecycle.2.2.2 unique blocked checked present built
    parentFound parentPhase anchorUse parentEarlier parentDifferent
  simpa only [committedExitState, ActiveChildUnique, ActiveChildParentBlocked, update] using candidates

#print axioms commit_replacement_landing_child_invariants
#print axioms completed_replacement_landing_child_invariants

end Goose.Proofs.ConstructionAcceptedExecution
