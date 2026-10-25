import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsLandingSupport

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

def OwnershipLandingParentChoice (state : ConstructionState) (root final : DestinationId)
    (anchor : PendingDestination) (update : Option (DestinationId × PendingDestination)) : Prop :=
  match anchor.use with
  | .receiver => update = none
  | .child parent => ∃ row count, state.destinations[parent]? = some row ∧
      row.progress = .suspended count root ∧ update = some (parent, {row with progress := .suspended count final})
  | .replacement parent => ∃ row count, state.destinations[parent]? = some row ∧
      row.progress = .exiting count root ∧ update = some (parent, {row with progress := .exiting count final})

theorem ownershipLandingParentChoice_fields (state : ConstructionState) (root final : DestinationId)
    (anchor : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (ordered : DestinationOwnersOrdered state) (present : state.destinations[root]? = some anchor)
    (choice : OwnershipLandingParentChoice state root final anchor update) :
    ∀ parent updated, update = some (parent, updated) → ∃ row count,
      state.destinations[parent]? = some row ∧ parent < root ∧
      ((row.progress = .suspended count root ∧ updated = {row with progress := .suspended count final}) ∨
        (row.progress = .exiting count root ∧ updated = {row with progress := .exiting count final})) := by
  intro parent updated selected
  cases use : anchor.use with
  | receiver =>
      simp only [OwnershipLandingParentChoice, use] at choice
      rw [choice] at selected
      cases selected
  | child owner | replacement owner =>
      simp only [OwnershipLandingParentChoice, use] at choice
      obtain ⟨row, count, rowPresent, progress, exactUpdate⟩ := choice
      rw [exactUpdate] at selected
      cases selected
      refine ⟨row, count, rowPresent, ?_, ?_⟩
      · simpa only [use] using ordered root anchor present
      · first | exact Or.inl ⟨progress, rfl⟩ | exact Or.inr ⟨progress, rfl⟩

theorem ownershipLandingParentChoice_parent (state : ConstructionState) (root final : DestinationId)
    (anchor : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (ordered : DestinationOwnersOrdered state) (present : state.destinations[root]? = some anchor)
    (choice : OwnershipLandingParentChoice state root final anchor update) : ProtectedRewireParent state root update := by
  intro parent updated selected
  obtain ⟨row, count, rowPresent, earlier, ⟨progress, rfl⟩ | ⟨progress, rfl⟩⟩ :=
    ownershipLandingParentChoice_fields state root final anchor update ordered present choice parent updated selected
  all_goals exact ⟨row, rowPresent, rfl, earlier⟩

theorem ownershipLandingParentChoice_active (state : ConstructionState) (root final : DestinationId)
    (anchor : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (ordered : DestinationOwnersOrdered state) (present : state.destinations[root]? = some anchor)
    (choice : OwnershipLandingParentChoice state root final anchor update) :
    ∀ parent updated, update = some (parent, updated) → ∃ row : PendingDestination,
      state.destinations[parent]? = some row ∧ activeProgress row.progress = true := by
  intro parent updated selected
  obtain ⟨row, count, rowPresent, earlier, ⟨progress, rfl⟩ | ⟨progress, rfl⟩⟩ :=
    ownershipLandingParentChoice_fields state root final anchor update ordered present choice parent updated selected
  all_goals exact ⟨row, rowPresent, by simp only [progress, activeProgress]⟩

end Goose.Proofs.ConstructionExecutionOwnership
