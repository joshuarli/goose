import Goose.Construct.Runtime
import Goose.Proofs.ConstructionExecutionOwnershipLinks

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

inductive ReplacementSupported (state : ConstructionState) : DestinationId → Prop
  | active (id : DestinationId) (row : PendingDestination)
      (present : state.destinations[id]? = some row) (live : activeProgress row.progress = true) :
      ReplacementSupported state id
  | parent (id parent : DestinationId) (row : PendingDestination)
      (present : state.destinations[id]? = some row) (use : row.use = .replacement parent)
      (supported : ReplacementSupported state id) : ReplacementSupported state parent

def SupportedReplacementAuthority (state : ConstructionState) : Prop :=
  ∀ (id parent : DestinationId) (row : PendingDestination),
    state.destinations[id]? = some row → row.use = .replacement parent →
    ReplacementSupported state id →
    ∃ owner, state.destinations[parent]? = some owner ∧ row.backing = owner.backing ∧
      ((∃ count, owner.progress = .exiting count id) ∨ owner.progress = .abandoned ∨
        owner.progress = .cancelled)

def ReplacementSupportExtension (before after : ConstructionState) : Prop :=
  ∀ id, id < before.destinations.size → ReplacementSupported after id → ReplacementSupported before id

theorem replacementSupported_parent (state : ConstructionState) (id parent : DestinationId)
    (row : PendingDestination) (present : state.destinations[id]? = some row)
    (use : row.use = .replacement parent) (supported : ReplacementSupported state id) :
    ReplacementSupported state parent :=
  .parent id parent row present use supported

theorem active_replacement_original_exact (state : ConstructionState)
    (valid : SupportedReplacementAuthority state) (id parent : DestinationId)
    (row : PendingDestination) (present : state.destinations[id]? = some row)
    (use : row.use = .replacement parent) (live : activeProgress row.progress = true) :
    ∃ owner, state.destinations[parent]? = some owner ∧ row.backing = owner.backing ∧
      ((∃ count, owner.progress = .exiting count id) ∨ owner.progress = .abandoned ∨
        owner.progress = .cancelled) :=
  valid id parent row present use (.active id row present live)

theorem supported_replacement_original_backing (state : ConstructionState)
    (valid : SupportedReplacementAuthority state) (id parent : DestinationId)
    (row owner : PendingDestination) (present : state.destinations[id]? = some row)
    (use : row.use = .replacement parent) (supported : ReplacementSupported state id)
    (ownerPresent : state.destinations[parent]? = some owner) : row.backing = owner.backing := by
  obtain ⟨actual, found, backing, _⟩ := valid id parent row present use supported
  cases Option.some.inj (found.symm.trans ownerPresent)
  exact backing

theorem initial_supportedReplacementAuthority : SupportedReplacementAuthority .initial := by
  intro id parent row present
  simp [ConstructionState.initial] at present

theorem replacementSupportExtension_refl (state : ConstructionState) :
    ReplacementSupportExtension state state := by
  intro id _ supported
  exact supported

theorem replacementSupportExtension_trans (before middle after : ConstructionState)
    (size : before.destinations.size ≤ middle.destinations.size)
    (first : ReplacementSupportExtension before middle)
    (second : ReplacementSupportExtension middle after) : ReplacementSupportExtension before after := by
  intro id inside supported
  exact first id inside (second id (Nat.lt_of_lt_of_le inside size) supported)

end Goose.Proofs.ConstructionExecutionOwnership
