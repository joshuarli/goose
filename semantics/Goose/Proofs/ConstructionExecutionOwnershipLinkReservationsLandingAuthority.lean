import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsLandingMetadata

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem protectedCleanupRewire_supportedReplacementAuthority (state : ConstructionState)
    (root final : DestinationId) (landed anchor finalRow : PendingDestination)
    (update : Option (DestinationId × PendingDestination))
    (valid : DestinationLifecycleInvariant state) (authority : SupportedReplacementAuthority state)
    (earlier : root < final) (anchorPresent : state.destinations[root]? = some anchor)
    (finalPresent : state.destinations[final]? = some finalRow)
    (built : ∃ count, finalRow.progress = .built count)
    (sameUse : landed.use = anchor.use) (sameBacking : landed.backing = anchor.backing)
    (path : OwnershipReplacementPath state.destinations root final)
    (choice : OwnershipLandingParentChoice state root final anchor update) :
    SupportedReplacementAuthority (protectedCleanupRewireState state root final landed update) := by
  let after := protectedCleanupRewireState state root final landed update
  have inside := (Array.getElem?_eq_some_iff.mp finalPresent).1
  have parents := ownershipLandingParentChoice_parent state root final anchor update valid.2.2.2 anchorPresent choice
  have parentActive := ownershipLandingParentChoice_active state root final anchor update valid.2.2.2 anchorPresent choice
  have live : activeProgress finalRow.progress = true := by
    obtain ⟨count, progress⟩ := built
    simp only [progress, activeProgress]
  have finalSupported : ReplacementSupported state final := .active final finalRow finalPresent live
  have rootSupported := path.supported finalSupported
  have ownerBound : match landed.use with | .receiver => True | .child parent | .replacement parent => parent < final := by
    rw [sameUse]
    cases use : anchor.use with
    | receiver => trivial
    | child parent | replacement parent =>
        have bound : parent < root := by simpa only [use] using valid.2.2.2 root anchor anchorPresent
        exact Nat.lt_trans bound earlier
  have outside : ∀ parent, landed.use = .replacement parent → parent < root := by
    intro parent use
    have anchorUse := sameUse.symm.trans use
    simpa only [anchorUse] using valid.2.2.2 root anchor anchorPresent
  have unsupported := protectedCleanup_rewire_unsupported state root final landed update valid inside earlier parents ownerBound outside
  have finalAfter := (protectedCleanupRewire_reads state root final landed update valid inside earlier parents).2
  intro index parent row present use supported
  by_cases finalIndex : index = final
  · subst index
    cases Option.some.inj (present.symm.trans finalAfter)
    have anchorUse := sameUse.symm.trans use
    obtain ⟨owner, ownerPresent, backing, phase⟩ := authority root parent anchor anchorPresent anchorUse rootSupported
    simp only [OwnershipLandingParentChoice, anchorUse] at choice
    obtain ⟨current, count, currentPresent, progress, rfl⟩ := choice
    cases Option.some.inj (currentPresent.symm.trans ownerPresent)
    have size := (abandonRowsState_frame (protectedRows state root final) state).2.2.1
    have parentInside : parent < ((abandonRowsState (protectedRows state root final) state).destinations.set! final landed).size := by
      simpa only [Array.size_set!, size] using (Array.getElem?_eq_some_iff.mp ownerPresent).1
    refine ⟨{owner with progress := .exiting count final}, ?_, sameBacking.trans backing, Or.inl ⟨count, rfl⟩⟩
    exact Array.getElem?_setIfInBounds_self_of_lt parentInside
  · obtain ⟨original, originalPresent, metadata, phase⟩ :=
      protectedCleanupRewire_metadata state root final landed anchor update valid earlier anchorPresent choice index row finalIndex present
    have originalUse : original.use = .replacement parent :=
      (congrArg PendingDestination.use metadata).symm.trans use
    have originalSupport := protectedCleanupRewire_support_back state root final landed anchor finalRow update valid earlier parents
      parentActive finalPresent live anchorPresent sameUse path index supported
    obtain ⟨owner, ownerPresent, backing, ownerPhase⟩ := authority index parent original originalPresent originalUse originalSupport
    have parentDifferent : parent ≠ final := by
      intro equal
      subst parent
      cases Option.some.inj (ownerPresent.symm.trans finalPresent)
      obtain ⟨count, progress⟩ := built
      rcases ownerPhase with ⟨other, exiting⟩ | abandoned | cancelled
      all_goals simp [progress] at *
    obtain ⟨newOwner, newOwnerPresent⟩ := protectedCleanupRewire_existing state root final landed update parent owner ownerPresent
    obtain ⟨oldOwner, oldOwnerPresent, ownerMetadata, newPhase⟩ :=
      protectedCleanupRewire_metadata state root final landed anchor update valid earlier anchorPresent choice parent newOwner parentDifferent newOwnerPresent
    have oldOwnerEqual := Option.some.inj (oldOwnerPresent.symm.trans ownerPresent)
    subst oldOwner
    refine ⟨newOwner, newOwnerPresent, ?_, ?_⟩
    · exact (congrArg PendingDestination.backing metadata).trans
        (backing.trans (congrArg PendingDestination.backing ownerMetadata).symm)
    · rcases newPhase with unchanged | abandoned | ⟨count, suspended, updated⟩ | ⟨count, exiting, updated⟩
      · simpa only [unchanged] using ownerPhase
      · exact Or.inr (Or.inl abandoned)
      · rcases ownerPhase with ⟨other, old⟩ | old | old
        all_goals simp [suspended] at old
      · rcases ownerPhase with ⟨other, old⟩ | old | old
        · have equal : root = index := (DestinationProgress.exiting.inj (exiting.symm.trans old)).2
          subst index
          exact False.elim (unsupported supported)
        all_goals simp [exiting] at old

end Goose.Proofs.ConstructionExecutionOwnership
