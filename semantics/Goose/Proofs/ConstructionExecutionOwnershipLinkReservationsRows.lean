import Goose.Proofs.ConstructionExecutionOwnershipLinkRows

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

def OwnershipExitingMetadataFrame (before after : ConstructionState) : Prop :=
  ∀ (id : DestinationId) (initial final : PendingDestination),
    before.destinations[id]? = some initial → after.destinations[id]? = some final →
    ∀ count selected, initial.progress = .exiting count selected →
      ∀ finalCount finalSelected, final.progress = .exiting finalCount finalSelected →
        {final with progress := initial.progress} = initial

theorem OwnershipLinkRowsFrame.exitingMetadata {before after : ConstructionState}
    (frame : OwnershipLinkRowsFrame before after) : OwnershipExitingMetadataFrame before after := by
  intro id initial final initialPresent finalPresent count selected initialExiting finalCount finalSelected finalExiting
  have same := frame.exiting id initial final initialPresent finalPresent count selected initialExiting
    finalCount finalSelected finalExiting
  subst final
  rfl

theorem ownershipExitingMetadataFrame_refl (state : ConstructionState) :
    OwnershipExitingMetadataFrame state state := (OwnershipLinkRowsFrame.refl state).exitingMetadata

theorem ownershipExitingMetadataFrame_replace_progress (state : ConstructionState) (id : DestinationId)
    (before : PendingDestination) (progress : DestinationProgress)
    (present : state.destinations[id]? = some before) :
    OwnershipExitingMetadataFrame state
      {state with destinations := state.destinations.set! id {before with progress := progress}} := by
  intro index initial final initialPresent finalPresent _ _ _ _ _ _
  by_cases same : id = index
  · subst index
    have initialEqual := Option.some.inj (initialPresent.symm.trans present)
    subst initial
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    have finalEqual : {before with progress := progress} = final := by
      simpa only [Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt inside, Option.some.injEq] using finalPresent
    subst final
    rfl
  · have original : state.destinations[index]? = some final := by
      simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using finalPresent
    have equal := Option.some.inj (original.symm.trans initialPresent)
    subst final
    rfl

theorem OwnershipExitingMetadataFrame.trans {before middle after : ConstructionState}
    (firstMetadata : ReservationMetadataFrame before middle)
    (secondMetadata : ReservationMetadataFrame middle after)
    (first : OwnershipExitingMetadataFrame before middle)
    (second : OwnershipExitingMetadataFrame middle after) : OwnershipExitingMetadataFrame before after := by
  intro id initial final initialPresent finalPresent count selected initialExiting finalCount finalSelected finalExiting
  have inside := (Array.getElem?_eq_some_iff.mp initialPresent).1
  have middleInside := Nat.lt_of_lt_of_le inside firstMetadata.destinations
  let interim := middle.destinations[id]
  have interimPresent : middle.destinations[id]? = some interim := Array.getElem?_eq_getElem middleInside
  obtain ⟨interimStable, _⟩ := firstMetadata.rows.preserves id initial interim initialPresent interimPresent
    (by simp [ReservationStableProgress, initialExiting])
  obtain ⟨_, interimExiting⟩ :=
    secondMetadata.rows.preserves id interim final interimPresent finalPresent interimStable
  obtain ⟨midCount, midSelected, midExiting, _⟩ := interimExiting finalCount finalSelected finalExiting
  have last := second id interim final interimPresent finalPresent midCount midSelected midExiting
    finalCount finalSelected finalExiting
  have start := first id initial interim initialPresent interimPresent count selected initialExiting
    midCount midSelected midExiting
  exact (congrArg (fun row : PendingDestination => {row with progress := initial.progress}) last).trans start

theorem freshReservationSnapshotAuthority_metadata_frame (before after : ConstructionState)
    (valid : ReservationLifecycleInvariant before) (frame : ReservationMetadataFrame before after)
    (rows : OwnershipExitingMetadataFrame before after)
    (authority : FreshReservationSnapshotAuthority before) : FreshReservationSnapshotAuthority after := by
  intro token incoming selected snapshot current ticket different currentPresent count replacement exiting
  rw [frame.tickets] at ticket
  have active := valid.2.active token .fresh incoming selected snapshot ticket
  have originalInside := active.1.allocated
  let original := before.destinations[snapshot.capability.id]
  have originalPresent : before.destinations[snapshot.capability.id]? = some original :=
    Array.getElem?_eq_getElem originalInside
  have phase := (active.2.2.2 (Ne.symm different)).2 original originalPresent
  have stable : ReservationStableProgress original.progress := by
    cases progress : original.progress <;>
      simp_all only [ReservedSnapshotPhase, ReservationStableProgress]
  obtain ⟨_, previous⟩ := frame.rows.preserves snapshot.capability.id original current originalPresent currentPresent stable
  obtain ⟨oldCount, oldSelected, oldExiting, _⟩ := previous count replacement exiting
  have same := rows snapshot.capability.id original current originalPresent currentPresent
    oldCount oldSelected oldExiting count replacement exiting
  have initial := authority token incoming selected snapshot original ticket different originalPresent
    oldCount oldSelected oldExiting
  calc
    {current with progress := snapshot.progress} =
        {{current with progress := original.progress} with progress := snapshot.progress} := rfl
    _ = {original with progress := snapshot.progress} := congrArg
      (fun row : PendingDestination => {row with progress := snapshot.progress}) same
    _ = snapshot := initial

theorem constructionOwnershipLinks_metadata_frame (before after : ConstructionState)
    (reservation : ReservationLifecycleInvariant before) (valid : ConstructionOwnershipLinks before)
    (metadata : ReservationMetadataFrame before after) (children : OwnershipChildSourceExtension before after) (exiting : OwnershipExitingMetadataFrame before after)
    (bounded : DestinationLifecycleInvariant after) (forward : DestinationForwardLinks after) :
    ConstructionOwnershipLinks after := by
  rcases valid with ⟨_, _, saved, fresh, authority, direct, resumed⟩
  refine ⟨bounded, forward, ⟨?_, ?_⟩, ?_,
    freshReservationSnapshotAuthority_metadata_frame before after reservation metadata exiting authority, ?_, ?_⟩
  · intro token incoming selected snapshot present
    rw [metadata.tickets] at present
    obtain ⟨count, opened | built | suspended⟩ := fresh token incoming selected snapshot present
    · exact destinationForwardLink_childSourceExtension before after children _ _
        (by simp [SavedDestinationProgress, opened]) (saved.1 token incoming selected snapshot present)
    · exact destinationForwardLink_childSourceExtension before after children _ _
        (by simp [SavedDestinationProgress, built]) (saved.1 token incoming selected snapshot present)
    · obtain ⟨child, suspended⟩ := suspended
      exact destinationForwardLink_childSourceExtension before after children _ _
        (by simp [SavedDestinationProgress, suspended]) (saved.1 token incoming selected snapshot present)
  · intro id snapshot present
    rw [metadata.resumptions] at present
    simp only [DestinationForwardLink, resumed id snapshot present]
  · intro token incoming selected snapshot present
    rw [metadata.tickets] at present
    exact fresh token incoming selected snapshot present
  · intro token incoming selected snapshot present same
    rw [metadata.tickets] at present
    exact direct token incoming selected snapshot present same
  · intro id snapshot present
    rw [metadata.resumptions] at present
    exact resumed id snapshot present

end Goose.Proofs.ConstructionExecutionOwnership
