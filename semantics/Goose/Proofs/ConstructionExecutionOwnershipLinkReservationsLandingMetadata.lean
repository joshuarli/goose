import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupMetadata
import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsLandingParent

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

def OwnershipLandingProgress (root final : DestinationId) (before after : DestinationProgress) : Prop :=
  after = before ∨ after = .abandoned ∨
    (∃ count, before = .suspended count root ∧ after = .suspended count final) ∨
    (∃ count, before = .exiting count root ∧ after = .exiting count final)

theorem protectedCleanupRewire_metadata (state : ConstructionState) (root final : DestinationId)
    (landed anchor : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (valid : DestinationLifecycleInvariant state) (earlier : root < final)
    (anchorPresent : state.destinations[root]? = some anchor)
    (choice : OwnershipLandingParentChoice state root final anchor update)
    (id : DestinationId) (row : PendingDestination) (different : id ≠ final)
    (present : (protectedCleanupRewireState state root final landed update).destinations[id]? = some row) :
    ∃ original, state.destinations[id]? = some original ∧
      {row with progress := original.progress} = original ∧
      OwnershipLandingProgress root final original.progress row.progress := by
  have clean (found : (abandonRowsState (protectedRows state root final) state).destinations[id]? = some row) :
      ∃ original, state.destinations[id]? = some original ∧
        {row with progress := original.progress} = original ∧
        OwnershipLandingProgress root final original.progress row.progress := by
    obtain ⟨original, originalPresent, metadata, phase⟩ := abandonRowsState_metadata_lookup
      (protectedRows state root final) state (protectedRows_current state root final valid.2.1)
      (protectedRows_indexed state root final valid.2.1).2 id row found
    refine ⟨original, originalPresent, metadata, ?_⟩
    rcases phase with unchanged | abandoned
    · exact Or.inl unchanged
    · exact Or.inr (Or.inl abandoned)
  cases update with
  | none =>
      apply clean
      simpa only [protectedCleanupRewireState, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne (Ne.symm different)] using present
  | some pair =>
      obtain ⟨parent, updated⟩ := pair
      by_cases same : parent = id
      · subst id
        obtain ⟨original, count, originalPresent, parentEarlier, phase⟩ :=
          ownershipLandingParentChoice_fields state root final anchor _ valid.2.2.2 anchorPresent choice parent updated rfl
        have size := (abandonRowsState_frame (protectedRows state root final) state).2.2.1
        have inside : parent < ((abandonRowsState (protectedRows state root final) state).destinations.set! final landed).size := by
          simpa only [Array.size_set!, size] using (Array.getElem?_eq_some_iff.mp originalPresent).1
        have equal : updated = row := Option.some.inj ((Array.getElem?_setIfInBounds_self_of_lt inside).symm.trans present)
        subst row
        rcases phase with ⟨old, rfl⟩ | ⟨old, rfl⟩
        · exact ⟨original, originalPresent, rfl, Or.inr (Or.inr (Or.inl ⟨count, old, rfl⟩))⟩
        · exact ⟨original, originalPresent, rfl, Or.inr (Or.inr (Or.inr ⟨count, old, rfl⟩))⟩
      · apply clean
        simpa only [protectedCleanupRewireState, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne same,
          Array.getElem?_setIfInBounds_ne (Ne.symm different)] using present

theorem protectedCleanupRewire_size (state : ConstructionState) (root final : DestinationId)
    (landed : PendingDestination) (update : Option (DestinationId × PendingDestination)) :
    (protectedCleanupRewireState state root final landed update).destinations.size = state.destinations.size := by
  cases update with
  | none => exact (Array.size_set! ..).trans (abandonRowsState_frame _ state).2.2.1
  | some pair => exact (Array.size_set! ..).trans ((Array.size_set! ..).trans (abandonRowsState_frame _ state).2.2.1)

theorem protectedCleanupRewire_existing (state : ConstructionState) (root final : DestinationId)
    (landed : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (id : DestinationId) (row : PendingDestination) (present : state.destinations[id]? = some row) :
    ∃ after, (protectedCleanupRewireState state root final landed update).destinations[id]? = some after := by
  have inside : id < (protectedCleanupRewireState state root final landed update).destinations.size := by
    rw [protectedCleanupRewire_size]
    exact (Array.getElem?_eq_some_iff.mp present).1
  exact ⟨_, Array.getElem?_eq_getElem inside⟩

end Goose.Proofs.ConstructionExecutionOwnership
