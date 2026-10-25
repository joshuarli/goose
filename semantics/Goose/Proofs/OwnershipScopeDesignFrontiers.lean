import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsAuthority
import Goose.Proofs.ConstructionExecutionProtocolOwnersAncestry

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

def CarriedReservationBranch (state : ConstructionState) (selected : DestinationId)
    (carried : List DestinationId) : Prop :=
  carried.any (destinationDescendant state.destinations selected) = true

def ResidualReservationFrontiers (state : ConstructionState) (carried : List DestinationId) : Prop :=
  ∀ (token : ExitReservationId) (incoming reserved selected : DestinationId)
    (snapshot destination : PendingDestination),
    state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
    destinationCurrent state reserved = .ok selected →
    state.destinations[selected]? = some destination →
    activeProgress destination.progress = false →
    ReplacementSupported state selected → CarriedReservationBranch state selected carried

theorem initial_residualReservationFrontiers (carried : List DestinationId) :
    ResidualReservationFrontiers .initial carried := by
  intro token incoming reserved selected snapshot destination ticket
  simp [ConstructionState.initial] at ticket

theorem carriedReservationBranch_mono (state : ConstructionState) (selected : DestinationId)
    (before after : List DestinationId) (included : ∀ id ∈ before, id ∈ after)
    (carriedBranch : CarriedReservationBranch state selected before) :
    CarriedReservationBranch state selected after := by
  obtain ⟨id, member, descendant⟩ := List.any_eq_true.mp carriedBranch
  exact List.any_eq_true.mpr ⟨id, included id member, descendant⟩

theorem residualReservationFrontiers_mono (state : ConstructionState)
    (before after : List DestinationId) (included : ∀ id ∈ before, id ∈ after)
    (frontiers : ResidualReservationFrontiers state before) :
    ResidualReservationFrontiers state after := by
  intro token incoming reserved selected snapshot destination ticket current present inactive supported
  exact carriedReservationBranch_mono state selected before after included
    (frontiers token incoming reserved selected snapshot destination ticket current present inactive supported)

theorem residualReservationFrontiers_no_support (state : ConstructionState)
    (carried : List DestinationId) (frontiers : ResidualReservationFrontiers state carried)
    (token : ExitReservationId) (incoming reserved selected : DestinationId)
    (snapshot destination : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (current : destinationCurrent state reserved = .ok selected)
    (present : state.destinations[selected]? = some destination)
    (inactive : activeProgress destination.progress = false)
    (unprotected : ¬ CarriedReservationBranch state selected carried) :
    ¬ ReplacementSupported state selected := by
  intro supported
  exact unprotected (frontiers token incoming reserved selected snapshot destination
    ticket current present inactive supported)

theorem cancelExitReservation_carried_branch (state : ConstructionState)
    (carried : List DestinationId) (token : ExitReservationId)
    (incoming reserved selected : DestinationId) (snapshot : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (current : destinationCurrent state reserved = .ok selected)
    (carriedBranch : CarriedReservationBranch state selected carried) :
    cancelExitReservation token carried state = .ok () state := by
  unfold CarriedReservationBranch destinationDescendant at carriedBranch
  simp only [cancelExitReservation, ConstructionM.get, bind, ticket, current, pure,
    carriedBranch, ↓reduceIte]

theorem cancelExitReservation_supported_inactive (state : ConstructionState)
    (carried : List DestinationId) (frontiers : ResidualReservationFrontiers state carried)
    (token : ExitReservationId) (incoming reserved selected : DestinationId)
    (snapshot destination : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (current : destinationCurrent state reserved = .ok selected)
    (present : state.destinations[selected]? = some destination)
    (inactive : activeProgress destination.progress = false)
    (supported : ReplacementSupported state selected) :
    cancelExitReservation token carried state = .ok () state :=
  cancelExitReservation_carried_branch state carried token incoming reserved selected snapshot ticket current
    (frontiers token incoming reserved selected snapshot destination ticket current present inactive supported)

theorem supportedReplacementAuthority_restore_exiting (state : ConstructionState)
    (id selected count : DestinationId) (before snapshot : PendingDestination)
    (present : state.destinations[id]? = some before)
    (exiting : before.progress = .exiting count selected)
    (sameUse : snapshot.use = before.use) (sameBacking : snapshot.backing = before.backing)
    (unsupported : ¬ ReplacementSupported state selected)
    (valid : SupportedReplacementAuthority state) :
    SupportedReplacementAuthority { state with destinations := state.destinations.set! id snapshot } := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  intro index parent row found use supported
  have previousSupport := replacementSupported_replace_back state id before snapshot present
    (fun _ original => sameUse.symm.trans original)
    (by intro _; simp [exiting, activeProgress]) index supported
  have previous : ∃ initial, state.destinations[index]? = some initial ∧
      initial.use = .replacement parent ∧ row.backing = initial.backing := by
    by_cases same : id = index
    · subst index
      have equal : snapshot = row := by
        simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside,
          Option.some.injEq] using found
      subst row
      exact ⟨before, present, sameUse.symm.trans use, sameBacking⟩
    · exact ⟨row, by simpa only [Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne same] using found, use, rfl⟩
  obtain ⟨initial, initialPresent, initialUse, rowBacking⟩ := previous
  obtain ⟨owner, ownerPresent, backing, phase⟩ :=
    valid index parent initial initialPresent initialUse previousSupport
  have different : id ≠ parent := by
    intro same
    subst parent
    have equal : before = owner := Option.some.inj (present.symm.trans ownerPresent)
    subst owner
    rcases phase with ⟨oldCount, oldProgress⟩ | abandoned | cancelled
    · have target : selected = index := by
        have equal := exiting.symm.trans oldProgress
        exact (DestinationProgress.exiting.inj equal).2
      exact unsupported (target.symm ▸ previousSupport)
    · simp [exiting] at abandoned
    · simp [exiting] at cancelled
  exact ⟨owner, by simpa only [Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_ne different] using ownerPresent, rowBacking.trans backing, phase⟩

theorem restoreFreshSnapshot_supportedReplacementAuthority (state : ConstructionState)
    (carried : List DestinationId) (frontiers : ResidualReservationFrontiers state carried)
    (token : ExitReservationId) (incoming reserved selected count : DestinationId)
    (snapshot destination superseded : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (current : destinationCurrent state reserved = .ok selected)
    (present : state.destinations[selected]? = some destination)
    (inactive : activeProgress destination.progress = false)
    (unprotected : ¬ CarriedReservationBranch state selected carried)
    (ownerPresent : state.destinations[snapshot.capability.id]? = some superseded)
    (ownerExiting : superseded.progress = .exiting count selected)
    (different : reserved ≠ snapshot.capability.id)
    (links : ConstructionOwnershipLinks state) (authority : SupportedReplacementAuthority state) :
    SupportedReplacementAuthority
      { state with destinations := state.destinations.set! snapshot.capability.id snapshot } := by
  have snapshotAuthority := links.2.2.2.2.1 token incoming reserved snapshot superseded
    ticket different ownerPresent count selected ownerExiting
  apply supportedReplacementAuthority_restore_exiting state snapshot.capability.id selected count
    superseded snapshot ownerPresent ownerExiting
    (by simpa using (congrArg PendingDestination.use snapshotAuthority).symm)
    (by simpa using (congrArg PendingDestination.backing snapshotAuthority).symm)
    (residualReservationFrontiers_no_support state carried frontiers token incoming reserved selected
      snapshot destination ticket current present inactive unprotected) authority

#print axioms cancelExitReservation_supported_inactive
#print axioms supportedReplacementAuthority_restore_exiting
#print axioms restoreFreshSnapshot_supportedReplacementAuthority

end Goose.Proofs.ConstructionExecutionOwnership
