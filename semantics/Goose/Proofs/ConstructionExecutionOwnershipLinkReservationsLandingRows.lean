import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsLandingForward
import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsRows

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem protectedCleanupRewire_children (state : ConstructionState) (root final : DestinationId)
    (landed anchor finalRow : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (valid : DestinationLifecycleInvariant state) (earlier : root < final)
    (anchorPresent : state.destinations[root]? = some anchor)
    (finalPresent : state.destinations[final]? = some finalRow)
    (replacement : ∃ original, finalRow.use = .replacement original)
    (choice : OwnershipLandingParentChoice state root final anchor update) :
    OwnershipChildSourceExtension state (protectedCleanupRewireState state root final landed update) := by
  intro id parent row present child
  have different : id ≠ final := by
    intro same
    subst id
    cases Option.some.inj (present.symm.trans finalPresent)
    obtain ⟨original, use⟩ := replacement
    simp [child] at use
  obtain ⟨current, currentPresent⟩ := protectedCleanupRewire_existing state root final landed update id row present
  obtain ⟨original, originalPresent, metadata, _⟩ := protectedCleanupRewire_metadata state root final landed anchor update
    valid earlier anchorPresent choice id current different currentPresent
  have equal := Option.some.inj (originalPresent.symm.trans present)
  subst original
  exact ⟨current, currentPresent, (congrArg PendingDestination.use metadata).trans child,
    by
      have backing := congrArg PendingDestination.backing metadata
      exact congrArg (fun backing => backing.receiverStorage) backing⟩

theorem protectedCleanupRewire_exitingMetadata (state : ConstructionState) (root final : DestinationId)
    (landed anchor finalRow : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (valid : DestinationLifecycleInvariant state) (earlier : root < final)
    (anchorPresent : state.destinations[root]? = some anchor)
    (finalPresent : state.destinations[final]? = some finalRow)
    (built : ∃ count, finalRow.progress = .built count)
    (choice : OwnershipLandingParentChoice state root final anchor update) :
    OwnershipExitingMetadataFrame state (protectedCleanupRewireState state root final landed update) := by
  intro id initial current initialPresent currentPresent count selected progress finalCount finalSelected finalProgress
  have different : id ≠ final := by
    intro same
    subst id
    cases Option.some.inj (initialPresent.symm.trans finalPresent)
    obtain ⟨originalCount, builtProgress⟩ := built
    simp [progress] at builtProgress
  obtain ⟨original, originalPresent, metadata, _⟩ := protectedCleanupRewire_metadata state root final landed anchor update
    valid earlier anchorPresent choice id current different currentPresent
  have equal := Option.some.inj (originalPresent.symm.trans initialPresent)
  subst original
  exact metadata

end Goose.Proofs.ConstructionExecutionOwnership
