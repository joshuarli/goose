import Goose.Proofs.ConstructionExitReleasedAppendContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Proofs.ConstructionAcceptedExecution

theorem released_append_live_preimage (state : ConstructionState) (token : Nat) (reservation : ExitReservation)
    (live : OwnershipReservationNeedsFrame reservation)
    (found : (state.exitReservations.push .released)[token]? = some reservation) :
    state.exitReservations[token]? = some reservation := by
  simp only [Array.getElem?_push] at found
  split at found
  · have same : reservation = .released := Option.some.inj found.symm
    subst reservation
    exact False.elim live
  · exact found

theorem captured_receiving_after_append_released (state : ConstructionState) (ambient : OwnershipAmbient)
    (bounds : OwnershipCapturedReceivingBounds state ambient) (valid : OwnershipCapturedReceivingFrames state ambient) :
    let after := { state with exitReservations := state.exitReservations.push .released }
    OwnershipCapturedReceivingBounds after ambient ∧ OwnershipCapturedReceivingFrames after ambient := by
  let after := { state with exitReservations := state.exitReservations.push .released }
  have within (outer : OwnershipAmbient) (receiving : Nat)
      (previous : OwnershipReceivingWithinSuccessorFrames state outer receiving) :
      OwnershipReceivingWithinSuccessorFrames after outer receiving := by
    intro frame member token owned incoming reserved snapshot node ticket aliases ancestry
    have old := released_append_live_preimage state token (.active .fresh incoming reserved snapshot) trivial ticket
    exact previous frame member token owned incoming reserved snapshot node old
      (DestinationSuccessorPath.congr (before := after) (after := state) rfl aliases) ancestry
  have channel (outer : OwnershipAmbient) (channel : Channel)
      (previous : OwnershipChannelReceivingWithinFrames state outer channel) :
      OwnershipChannelReceivingWithinFrames after outer channel := by
    have currentBefore (id receiving : Nat) (current : destinationCurrent after id = .ok receiving) :
        destinationCurrent state id = .ok receiving := by
      rw [destinationCurrent_congr_tables state after rfl rfl id] at current
      exact current
    cases channel with
    | register ty => trivial
    | construct id =>
      intro receiving current
      exact within outer receiving (previous receiving (currentBefore id receiving current))
    | completion token =>
      constructor
      · intro id ticket receiving current
        exact within outer receiving (previous.1 id (released_append_live_preimage state token (.waiting id) trivial ticket)
          receiving (currentBefore id receiving current))
      · intro role id reserved snapshot ticket receiving current
        exact within outer receiving (previous.2 role id reserved snapshot
          (released_append_live_preimage state token (.active role id reserved snapshot) trivial ticket)
          receiving (currentBefore reserved receiving current))
  have bound (c : Channel) (old : OwnershipChannelReceivingBound state c) : OwnershipChannelReceivingBound after c := by
    cases c with
    | register ty => trivial
    | construct id => exact old
    | completion token =>
      intro id ticket
      exact old id (released_append_live_preimage state token (.waiting id) trivial ticket)
  induction ambient with
  | nil => exact ⟨trivial, trivial⟩
  | cons frame outer ih =>
    obtain ⟨outerBounds, outerValid⟩ := ih bounds.2 valid.2
    refine ⟨⟨?_, outerBounds⟩, ⟨?_, outerValid⟩⟩
    · cases frame <;> try trivial
      case receivingScope capture carriers => exact bound (.construct capture.incoming) bounds.1
      all_goals intro c member; exact bound c (bounds.1 c member)
    · cases frame <;> try trivial
      case receivingScope capture carriers => exact channel outer (.construct capture.incoming) valid.1
      all_goals intro c member; exact channel outer c (valid.1 c member)

theorem released_ticket_append_context_unbounded (before : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipExecutionContext before ambient) :
    OwnershipExecutionContext { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push .released } } ambient := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting 0) } }
  let after := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push .released } }
  have waitingSource := waitExitDestination_source_state before.construction 0 valid.source
  have waiting : waited.construction.exitReservations[token]? = some (.waiting 0) := by simp [waited, token]
  have source := ownershipSource_after_waiting_release waited.construction token 0 waiting waitingSource
  have resultSource : OwnershipSourceState after.construction := by
    simpa [after, waited, token, Array.set!_eq_setIfInBounds, Array.setIfInBounds, Array.set_push] using source
  have captures := captured_receiving_after_append_released before.construction ambient valid.bounds valid.receiving
  have boundaries : OwnershipAmbientBoundaries after.construction ambient := by
    have go : ∀ frames, OwnershipAmbientBoundaries before.construction frames →
        OwnershipAmbientBoundaries after.construction frames := by
      intro frames old
      induction frames with
      | nil => trivial
      | cons frame outer ih =>
        refine ⟨?_, ih old.2⟩
        intro index incoming reserved selected snapshot member ticket current retained carried
        have oldTicket := released_append_live_preimage before.construction index (.active .fresh incoming reserved snapshot) trivial ticket
        have oldCurrent : destinationCurrent before.construction reserved = .ok selected := by
          rw [destinationCurrent_congr_tables before.construction after.construction rfl rfl reserved] at current
          exact current
        exact old.1 index incoming reserved selected snapshot member oldTicket oldCurrent retained carried
    exact go ambient valid.retention.boundaries
  have reservations : OwnershipReservationFrames after.construction ambient := by
    intro token reservation found live
    exact valid.reservations token reservation (released_append_live_preimage before.construction token reservation live found) live
  refine ⟨resultSource, ⟨resultSource.structural.1, ?_, boundaries⟩, ?_, reservations, captures.2, captures.1, ?_⟩
  · intro id row present inactive supported
    have oldSupport : ReplacementSupported before.construction id :=
      replacementSupported_congr_destinations after.construction before.construction rfl id supported
    exact valid.retention.anchors id row (by simpa [after] using present) inactive oldSupport
  · exact ⟨valid.runtime.activations, valid.runtime.breaks⟩
  · exact ⟨valid.identities.activations, valid.identities.breaks⟩

#print axioms released_ticket_append_context_unbounded

#print axioms released_append_live_preimage
#print axioms captured_receiving_after_append_released

end Goose.Proofs.ConstructionExecutionOwnership
