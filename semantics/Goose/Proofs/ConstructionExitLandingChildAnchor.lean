import Goose.Proofs.ConstructionExitLandingReplacementChildren

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem child_invariants_replace_add_child (before after : ConstructionState) (id owner : Nat)
    (old new parent : PendingDestination) (present : before.destinations[id]? = some old)
    (rows : after.destinations = before.destinations.set! id new)
    (newUse : new.use = .child owner) (parentFound : before.destinations[owner]? = some parent)
    (parentPhase : ChildParentPhase parent) (different : owner ≠ id)
    (samePhase : ChildParentPhase new ↔ ChildParentPhase old)
    (noSibling : ∀ (index : Nat) (row : PendingDestination), before.destinations[index]? = some row →
      row.use = .child owner → activeRow row = true → False)
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
  have recover : ∀ (index : Nat) (row : PendingDestination) (parentId : Nat), index ≠ id →
      after.destinations[index]? = some row → row.use = .child parentId → activeRow row = true →
      before.destinations[index]? = some row := by
    intro index row parentId distinct found use active
    simpa only [outside index distinct] using found
  constructor
  · intro parentId first second left right leftFound leftUse leftActive rightFound rightUse rightActive
    by_cases firstNew : first = id
    · subst first
      have equal := Option.some.inj (current.symm.trans leftFound)
      subst left
      have sameOwner := DestinationUse.child.inj (leftUse.symm.trans newUse)
      subst parentId
      by_cases secondNew : second = id
      · exact secondNew.symm
      · exact False.elim (noSibling second right (recover second right owner secondNew rightFound rightUse rightActive) rightUse rightActive)
    · by_cases secondNew : second = id
      · subst second
        have equal := Option.some.inj (current.symm.trans rightFound)
        subst right
        have sameOwner := DestinationUse.child.inj (rightUse.symm.trans newUse)
        subst parentId
        exact False.elim (noSibling first left (recover first left owner firstNew leftFound leftUse leftActive) leftUse leftActive)
      · exact unique parentId first second left right
          (recover first left parentId firstNew leftFound leftUse leftActive) leftUse leftActive
          (recover second right parentId secondNew rightFound rightUse rightActive) rightUse rightActive
  · intro index row parentId found use active
    by_cases isNew : index = id
    · subst index
      have equal := Option.some.inj (current.symm.trans found)
      subst row
      have sameOwner := DestinationUse.child.inj (use.symm.trans newUse)
      subst parentId
      exact ⟨parent, by rw [outside owner different]; exact parentFound, parentPhase⟩
    · have oldFound := recover index row parentId isNew found use active
      obtain ⟨oldParent, oldParentFound, oldPhase⟩ := blocked index row parentId oldFound use active
      by_cases parentIsNew : parentId = id
      · subst parentId
        have equal := Option.some.inj (present.symm.trans oldParentFound)
        subst oldParent
        exact ⟨new, current, samePhase.mpr oldPhase⟩
      · exact ⟨oldParent, by rw [outside parentId parentIsNew]; exact oldParentFound, oldPhase⟩

theorem completed_child_landing_child_invariants (state : ConstructionState)
    (id old count parentId parentCount : Nat) (replacement anchor parent : PendingDestination) (storage : ReceivingStorage)
    (indexed : DestinationCapabilitiesIndexed state) (ordered : DestinationOwnersOrdered state)
    (unique : ActiveChildUnique state) (blocked : ActiveChildParentBlocked state)
    (checked : ∃ rows, protectedExitDiscarded state old id = .ok rows)
    (present : state.destinations[id]? = some replacement) (replacementBuilt : replacement.progress = .built count)
    (anchorFound : state.destinations[old]? = some anchor) (anchorActive : activeRow anchor = true)
    (anchorUse : anchor.use = .child parentId) (different : old ≠ id)
    (parentFound : state.destinations[parentId]? = some parent) (parentPhase : parent.progress = .suspended parentCount old)
    (parentEarlier : parentId < old) (parentDifferent : parentId ≠ id) :
    ActiveChildUnique (completedLandingState state id old count replacement anchor storage
      (some (parentId, { parent with progress := .suspended parentCount id }))) ∧
      ActiveChildParentBlocked (completedLandingState state id old count replacement anchor storage
      (some (parentId, { parent with progress := .suspended parentCount id }))) := by
  let rows := protectedRows state old id
  let cleaned := abandonRowsState rows state
  let adopted := { cleaned with destinations := cleaned.destinations.set! id (landedReplacementRow replacement anchor count) }
  let reparented := { adopted with destinations := adopted.destinations.set! parentId { parent with progress := .suspended parentCount id } }
  have cleanup := abandonPreservingExit_exact state old id indexed checked
  have cleanUnique : ActiveChildUnique cleaned := abandonPreservingExit_preserves_unique_children state cleaned old id indexed unique cleanup
  have cleanBlocked : ActiveChildParentBlocked cleaned := abandonPreservingExit_preserves_blocked_children state cleaned old id indexed ordered blocked cleanup
  have cleanReplacement : cleaned.destinations[id]? = some replacement := by
    have unchanged := protectedCleanup_lookup_outside state old id id ordered (Or.inl rfl)
    exact unchanged.trans present
  have cleanParent : cleaned.destinations[parentId]? = some parent := by
    have unchanged := protectedCleanup_lookup_outside state old id parentId ordered (Or.inr parentEarlier)
    exact unchanged.trans parentFound
  have anchorInside := (Array.getElem?_eq_some_iff.mp anchorFound).1
  have anchorCorrect := indexed old anchor anchorFound
  have anchorMember : anchor ∈ rows := by
    apply (protectedRows_exact_selection state old id anchor).mpr
    refine ⟨Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨old, anchorFound⟩), ?_, ?_, anchorActive⟩
    · simpa only [anchorCorrect] using different
    · simpa only [anchorCorrect] using destinationDescendant_self state old anchorInside
  have noSibling : ∀ (index : Nat) (row : PendingDestination), cleaned.destinations[index]? = some row →
      row.use = .child parentId → activeRow row = true → False := by
    intro index row found use active
    have beforeFound := abandonRows_active_source state rows (protectedRows_indexed state old id indexed).1
      (protectedRows_indexed state old id indexed).2 index row found active
    have equal := unique parentId index old row anchor beforeFound use active anchorFound anchorUse anchorActive
    subst index
    have abandoned := abandonRowsState_inside rows state (protectedRows_indexed state old id indexed).1
      (protectedRows_indexed state old id indexed).2 anchor anchorMember
    rw [anchorCorrect] at abandoned
    have same := Option.some.inj (abandoned.symm.trans found)
    subst row
    simp [activeRow] at active
  have adoptedInvariants : ActiveChildUnique adopted ∧ ActiveChildParentBlocked adopted := by
    apply child_invariants_replace_add_child cleaned adopted id parentId replacement
      (landedReplacementRow replacement anchor count) parent cleanReplacement rfl _ cleanParent _ parentDifferent _ noSibling cleanUnique cleanBlocked
    · simp [landedReplacementRow, anchorUse]
    · exact Or.inl ⟨parentCount, old, parentPhase⟩
    · simp [ChildParentPhase, replacementBuilt, landedReplacementRow]
  have adoptedParent : adopted.destinations[parentId]? = some parent := by
    simpa [adopted, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm parentDifferent] using cleanParent
  have reparentedInvariants : ActiveChildUnique reparented ∧ ActiveChildParentBlocked reparented := by
    apply child_invariants_replace_progress adopted reparented parentId parent
      { parent with progress := .suspended parentCount id } adoptedParent rfl rfl _ _ adoptedInvariants.1 adoptedInvariants.2
    · simp [activeRow, parentPhase]
    · simp [ChildParentPhase, parentPhase]
  by_cases moving : anchor.capability.start < replacement.capability.start
  · simpa only [completedLandingState, moving, ↓reduceIte, ActiveChildUnique, ActiveChildParentBlocked, reparented, adopted] using reparentedInvariants
  · simpa only [completedLandingState, moving, ↓reduceIte, ActiveChildUnique, ActiveChildParentBlocked, reparented, adopted] using reparentedInvariants

private abbrev sourceActive : PendingDestination → Bool := landing_active_source

private theorem sourceActive_matches (row : PendingDestination) : sourceActive row = activeRow row := by
  cases row.progress <;> rfl

theorem protectedExitDiscarded_anchor_active (state : ConstructionState) (old id : Nat)
    (anchor : PendingDestination) (found : state.destinations[old]? = some anchor)
    (checked : ∃ rows, protectedExitDiscarded state old id = .ok rows) : activeRow anchor = true := by
  obtain ⟨rows, checked⟩ := checked
  simp only [protectedExitDiscarded, bind, pure, Except.bind, Except.pure] at checked
  repeat' first
    | contradiction
    | simp only [Except.bind, Except.pure, found] at checked
    | split at checked
  all_goals
    rename_i proof
    simp only [sourceActive_matches] at proof
    simp_all

theorem commit_child_landing_child_invariants (state : ConstructionState)
    (id old count parentId parentCount : Nat) (replacement anchor parent : PendingDestination)
    (storage : ReceivingStorage) (receiving : Option DestinationId) (chain : List DestinationId)
    (lifecycle : DestinationLifecycleInvariant state) (unique : ActiveChildUnique state)
    (blocked : ActiveChildParentBlocked state) (checked : ∃ rows, protectedExitDiscarded state old id = .ok rows)
    (present : state.destinations[id]? = some replacement) (built : replacement.progress = .built count)
    (stored : state.storage[replacement.storage]? = some storage)
    (selected : exitLandingAnchor (state.destinations.size + 1) id replacement.storage receiving state =
      .ok (old, anchor, chain) state)
    (anchorUse : anchor.use = .child parentId)
    (parentFound : state.destinations[parentId]? = some parent) (parentPhase : parent.progress = .suspended parentCount old)
    (startOrder : anchor.capability.start ≤ replacement.capability.start)
    (inside : replacement.capability.start ≤ storage.bytes.size) :
    ∃ after, commitExitReplacement receiving id state = .ok () after ∧
      ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  obtain ⟨_, anchorEarlier, anchorPresent⟩ := exitLandingAnchor_success _ _ _ _ state state old anchor chain selected
  have anchorActive := protectedExitDiscarded_anchor_active state old id anchor anchorPresent checked
  have parentEarlier : parentId < old := by simpa only [anchorUse] using lifecycle.2.2.2 old anchor anchorPresent
  have parentDifferent : parentId ≠ id := Nat.ne_of_lt (Nat.lt_trans parentEarlier anchorEarlier)
  have different : old ≠ id := Nat.ne_of_lt anchorEarlier
  let update := some (parentId, { parent with progress := .suspended parentCount id })
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
  have candidates := completed_child_landing_child_invariants state id old count parentId parentCount
    replacement anchor parent storage lifecycle.2.1 lifecycle.2.2.2 unique blocked checked present built
    anchorPresent anchorActive anchorUse different parentFound parentPhase parentEarlier parentDifferent
  simpa only [committedExitState, ActiveChildUnique, ActiveChildParentBlocked, update] using candidates

#print axioms protectedExitDiscarded_anchor_active
#print axioms commit_child_landing_child_invariants
#print axioms completed_child_landing_child_invariants
#print axioms child_invariants_replace_add_child

end Goose.Proofs.ConstructionAcceptedExecution
