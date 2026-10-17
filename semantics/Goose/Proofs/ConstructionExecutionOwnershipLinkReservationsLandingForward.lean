import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsLandingAuthority
import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem protectedCleanup_lookup_outside (state : ConstructionState) (root final id : DestinationId)
    (ordered : DestinationOwnersOrdered state) (outside : id = final ∨ id < root) :
    (abandonRowsState (protectedRows state root final) state).destinations[id]? = state.destinations[id]? := by
  apply abandonRowsState_outside
  intro row member same
  have selected := (protectedRows_exact_selection state root final row).mp member
  rcases outside with equal | earlier
  · exact selected.2.1 (same.trans equal)
  · have absent := destinationDescendant_false_of_lt state ordered root id earlier
    simpa only [same, absent, Bool.false_eq_true] using selected.2.2.1

theorem protectedCleanupRewire_forward (state : ConstructionState) (root final : DestinationId)
    (landed anchor finalRow : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (valid : DestinationLifecycleInvariant state) (authority : SupportedReplacementAuthority state)
    (forward : DestinationForwardLinks state) (earlier : root < final)
    (anchorPresent : state.destinations[root]? = some anchor)
    (finalPresent : state.destinations[final]? = some finalRow)
    (built : ∃ count, finalRow.progress = .built count)
    (landedBuilt : ∃ count, landed.progress = .built count)
    (sameUse : landed.use = anchor.use) (sameBacking : landed.backing = anchor.backing)
    (path : OwnershipReplacementPath state.destinations root final)
    (choice : OwnershipLandingParentChoice state root final anchor update) :
    DestinationForwardLinks (protectedCleanupRewireState state root final landed update) := by
  let cleaned := abandonRowsState (protectedRows state root final) state
  have size : cleaned.destinations.size = state.destinations.size := (abandonRowsState_frame _ state).2.2.1
  have cleanForward := (abandonRowsState_ownership_frame (protectedRows state root final) state
    (protectedRows_current state root final valid.2.1) (protectedRows_indexed state root final valid.2.1).2).2.2 forward
  have finalClean : cleaned.destinations[final]? = some finalRow :=
    (protectedCleanup_lookup_outside state root final final valid.2.2.2 (Or.inl rfl)).trans finalPresent
  obtain ⟨immediate, finalUse, priorPath⟩ : ∃ immediate,
      finalRow.use = .replacement immediate ∧ OwnershipReplacementPath state.destinations root immediate := by
    cases path with
    | refl => exact False.elim (Nat.lt_irrefl _ earlier)
    | step id parent ancestor row found use priorPath =>
        have equal := Option.some.inj (finalPresent.symm.trans found)
        subst row
        exact ⟨parent, use, priorPath⟩
  have live : activeProgress finalRow.progress = true := by
    obtain ⟨count, progress⟩ := built
    simp only [progress, activeProgress]
  obtain ⟨original, originalPresent, backing, phase⟩ :=
    authority final immediate finalRow finalPresent finalUse (.active final finalRow finalPresent live)
  have immediateEarlier : immediate < final := by simpa only [finalUse] using valid.2.2.2 final finalRow finalPresent
  have immediateInside : immediate < cleaned.destinations.size := by
    rw [size]
    exact (Array.getElem?_eq_some_iff.mp originalPresent).1
  let current := cleaned.destinations[immediate]
  have currentPresent : cleaned.destinations[immediate]? = some current := Array.getElem?_eq_getElem immediateInside
  have inactive := protectedCleanup_inactive state root final immediate original current valid.2.1 originalPresent
    (priorPath.descendant valid.2.2.2 (Array.getElem?_eq_some_iff.mp originalPresent).1)
    (Nat.ne_of_lt immediateEarlier) currentPresent
  have leaf : OwnershipLeafProgress current.progress := by
    cases progress : current.progress <;> simp_all [OwnershipLeafProgress, activeProgress]
  let adopted : ConstructionState := {cleaned with destinations := cleaned.destinations.set! final landed}
  have adoptedForward : DestinationForwardLinks adopted := destinationForwardLinks_adopt_replacement cleaned final immediate
    finalRow landed current finalClean currentPresent finalUse leaf (by
      obtain ⟨count, progress⟩ := landedBuilt
      simp only [progress, OwnershipLeafProgress]) cleanForward
  have finalInside : final < cleaned.destinations.size := (Array.getElem?_eq_some_iff.mp finalClean).1
  have landedPresent : adopted.destinations[final]? = some landed := Array.getElem?_setIfInBounds_self_of_lt finalInside
  cases update with
  | none => exact adoptedForward
  | some pair =>
      obtain ⟨parent, updated⟩ := pair
      obtain ⟨originalParent, count, parentPresent, parentEarlier, phase⟩ :=
        ownershipLandingParentChoice_fields state root final anchor _ valid.2.2.2 anchorPresent choice parent updated rfl
      have parentDifferent : final ≠ parent := Ne.symm (Nat.ne_of_lt (Nat.lt_trans parentEarlier earlier))
      have adoptedParent : adopted.destinations[parent]? = some originalParent := by
        simpa only [adopted, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne parentDifferent,
          cleaned, protectedCleanup_lookup_outside state root final parent valid.2.2.2 (Or.inr parentEarlier)] using parentPresent
      rcases phase with ⟨progress, rfl⟩ | ⟨progress, rfl⟩
      all_goals
        first
        | change DestinationForwardLinks {adopted with destinations := adopted.destinations.set! parent {originalParent with progress := .suspended count final}}
        | change DestinationForwardLinks {adopted with destinations := adopted.destinations.set! parent {originalParent with progress := .exiting count final}}
        first
        | apply destinationForwardLinks_replace_sources adopted parent originalParent
            {originalParent with progress := .suspended count final} adoptedParent rfl
            (by cases use : originalParent.use <;> simp [OwnershipLinkBacking, use]) adoptedForward
        | apply destinationForwardLinks_replace_sources adopted parent originalParent
            {originalParent with progress := .exiting count final} adoptedParent rfl
            (by cases use : originalParent.use <;> simp [OwnershipLinkBacking, use]) adoptedForward
        have oldLink := forward parent originalParent parentPresent
        simp only [DestinationForwardLink, progress] at oldLink ⊢
        obtain ⟨selected, selectedPresent, selectedUse, selectedBacking⟩ := oldLink
        have equal := Option.some.inj (selectedPresent.symm.trans anchorPresent)
        subst selected
        exact ⟨landed, landedPresent, sameUse.trans selectedUse, by simpa only [sameBacking, PendingDestination.storage] using selectedBacking⟩

end Goose.Proofs.ConstructionExecutionOwnership
