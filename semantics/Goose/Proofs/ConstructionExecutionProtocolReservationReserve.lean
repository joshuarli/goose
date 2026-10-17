import Goose.Proofs.ConstructionExecutionProtocolReservationTickets
import Goose.Proofs.ConstructionExecutionProtocolReservationOpen
import Goose.Proofs.ConstructionExecutionProtocolOpen
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataAllocation
import Goose.Proofs.ConstructionExecutionProtocolReceivingRenewMetadata
import Goose.Proofs.ConstructionExecutionProtocolReservationNamed
import Goose.Proofs.ConstructionExecutionProtocolReservationFrontier

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private abbrev lookupStep (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (lookupDestination_result id state)

private def reserveSnapshotStep (role : ExitReservationRole) (incoming current : DestinationId)
    (snapshot : PendingDestination) (direct : Bool) : ConstructionM (ExitReservationId × DestinationId) := do
  let selected ← if direct then pure current else openExitReplacement current
  let state ← ConstructionM.get
  let token := state.exitReservations.size
  ConstructionM.set {state with exitReservations := state.exitReservations.push (.active role incoming selected snapshot)}
  pure (token, selected)

private theorem reserveSnapshotStep_lifecycle (role : ExitReservationRole) (incoming current : DestinationId)
    (snapshot : PendingDestination) (direct : Bool) (state : ConstructionState)
    (present : state.destinations[current]? = some snapshot) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (reserveSnapshotStep role incoming current snapshot direct state).finalState := by
  cases direct with
  | true =>
      simp only [reserveSnapshotStep, ↓reduceIte, pure, bind, ConstructionM.get, ConstructionM.set,
        ConstructionResult.finalState]
      exact reservationLifecycleInvariant_push_direct state role incoming current snapshot present valid
  | false =>
      have frame := openExitReplacement_reservation_frame current state valid.1
      have kept : ReservationLifecycleInvariant (openExitReplacement current state).finalState :=
        ⟨openExitReplacement_destination_lifecycle_invariant current state valid.1,
          destinationReservationStateValid_frame state _ frame valid.2⟩
      simp only [reserveSnapshotStep, Bool.false_eq_true, ↓reduceIte]
      cases opened : openExitReplacement current state with
      | fault reason after => simpa only [opened, bind, ConstructionResult.finalState] using kept
      | ok selected after =>
          simp only [opened, ConstructionResult.finalState] at kept frame
          obtain ⟨fresh, allocated, progress, phase⟩ := openExitReplacement_snapshot state current selected snapshot after present opened valid.1
          have correct := valid.1.2.1 current snapshot present
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have originalPresent : state.destinations[snapshot.capability.id]? = some snapshot := by
            simpa only [correct] using present
          simp only [opened, bind, ConstructionM.get, ConstructionM.set, pure, ConstructionResult.finalState]
          apply reservationLifecycleInvariant_push_active after role incoming selected snapshot
          · exact (savedDestinationBounds_of_row state current snapshot present valid.1).mono frame.destinations frame.storage
          · exact allocated
          · rw [correct, fresh]
            exact Nat.le_of_lt inside
          · exact fun _ => ⟨progress, phase⟩
          · intro replaced index otherRole otherIncoming otherSelected otherSnapshot otherPresent otherReplaced
            rw [frame.tickets] at otherPresent
            have oldPhase := (valid.2.active index otherRole otherIncoming otherSelected otherSnapshot otherPresent).2.2.2 otherReplaced
            exact Ne.symm (reservedSnapshotPhase_ne_mutable state otherSnapshot snapshot originalPresent progress oldPhase.2)
          · exact kept

private theorem reserveLookup_lifecycle (role : ExitReservationRole) (incoming current : DestinationId)
    (chooseDirect : PendingDestination → Bool) (state : ConstructionState)
    (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant ((do
      let snapshot ← lookupStep current
      reserveSnapshotStep role incoming current snapshot (chooseDirect snapshot)) state).finalState := by
  simp only [lookupStep, lookupDestination_result, bind]
  cases present : state.destinations[current]? with
  | none => exact valid
  | some snapshot => exact reserveSnapshotStep_lifecycle role incoming current snapshot (chooseDirect snapshot) state present valid

theorem reserveExitDestination_reservation_lifecycle (incoming : DestinationId)
    (source : ExitSource) (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (reserveExitDestination incoming source state).finalState := by
  rw [reserveExitDestination_equation]
  apply constructionInvariant_bind ReservationLifecycleInvariant
  · exact renewReceivingDestination_reservation_lifecycle incoming
  · intro current after afterValid
    simp only [ConstructionM.get, bind]
    split
    · simp only [pure, bind]
      change ReservationLifecycleInvariant ((do
        let snapshot ← lookupStep current
        reserveSnapshotStep (.named .awaitingSource)
          incoming current snapshot
          ((match snapshot.progress with | .open 0 => true | _ => false) || (source == ExitSource.namedResult))) after).finalState
      exact reserveLookup_lifecycle _ incoming current _ after afterValid
    · apply constructionInvariant_bind ReservationLifecycleInvariant
      · intro queried queriedValid
        change ReservationLifecycleInvariant (exitFrontierAction _ current queried).finalState
        rw [exitFrontierAction_finalState]
        exact queriedValid
      · intro selected final finalValid
        change ReservationLifecycleInvariant ((do
          let snapshot ← lookupStep selected
          reserveSnapshotStep ExitReservationRole.fresh
            incoming selected snapshot
            ((match snapshot.progress with | .open 0 => true | _ => false) || (source == ExitSource.namedResult))) final).finalState
        exact reserveLookup_lifecycle _ incoming selected _ final finalValid
      · exact afterValid
  · exact valid

theorem waitExitDestination_reservation_lifecycle (incoming : DestinationId)
    (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (waitExitDestination incoming state).finalState := by
  constructor
  · exact valid.1
  · constructor
    · intro index role otherIncoming selected snapshot present
      simp only [waitExitDestination, ConstructionM.get, ConstructionM.set, bind, pure,
        ConstructionResult.finalState, Array.getElem?_push] at present
      split at present
      · simp at present
      · obtain ⟨bounds, allocated, earlier, phase⟩ := valid.2.active index role otherIncoming selected snapshot present
        exact ⟨bounds.mono (Nat.le_refl _) (Nat.le_refl _), allocated, earlier, phase⟩
    · intro first second role otherIncoming selected snapshot otherRole otherInput otherSelected otherSnapshot firstPresent secondPresent different firstReplaced secondReplaced
      simp only [waitExitDestination, ConstructionM.get, ConstructionM.set, bind, pure,
        ConstructionResult.finalState, Array.getElem?_push] at firstPresent secondPresent
      split at firstPresent
      · simp at firstPresent
      · split at secondPresent
        · simp at secondPresent
        · exact valid.2.distinct first second role otherIncoming selected snapshot otherRole otherInput otherSelected otherSnapshot
            firstPresent secondPresent different firstReplaced secondReplaced
    · intro entry member
      exact (valid.2.resumptions entry member).mono (Nat.le_refl _) (Nat.le_refl _)

theorem selectWaitingExitDestination_reservation_lifecycle (token : ExitReservationId) (source : ExitSource)
    (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (selectWaitingExitDestination token source state).finalState := by
  simp only [selectWaitingExitDestination, ConstructionM.get, bind]
  cases present : state.exitReservations[token]? with
  | none => exact valid
  | some reservation =>
      cases reservation with
      | active role incoming selected snapshot | restored | released => exact valid
      | waiting incoming =>
          have reserved := reserveExitDestination_reservation_lifecycle incoming source state valid
          change ReservationLifecycleInvariant ((do
            let (selected, snapshot) ← prepareExitDestinationAction incoming source
            let state ← ConstructionM.get
            ConstructionM.set {state with exitReservations := state.exitReservations.set! token (.active (if source == ExitSource.namedResult then .named .awaitingSource else .fresh) incoming selected snapshot)}
            pure selected) state).finalState
          cases prepared : prepareExitDestinationAction incoming source state with
          | fault reason after =>
              simpa only [reserveExitDestination, prepared, bind, ConstructionResult.finalState] using reserved
          | ok pair after =>
              rcases pair with ⟨selected, snapshot⟩
              simp only [reserveExitDestination, prepared, bind, ConstructionM.get, ConstructionM.set, pure,
                ConstructionResult.finalState] at reserved
              simp only [prepared, bind, ConstructionM.get, ConstructionM.set, pure, ConstructionResult.finalState]
              exact reservationLifecycleInvariant_replace_from_push after token _ incoming selected snapshot reserved

private theorem reserveSnapshotStep_fresh_tickets (incoming current : DestinationId)
    (snapshot : PendingDestination) (direct : Bool) (state : ConstructionState)
    (present : state.destinations[current]? = some snapshot)
    (progress : direct = true → SavedDestinationProgress snapshot.progress)
    (valid : ReservationLifecycleInvariant state) :
    let after := (reserveSnapshotStep .fresh incoming current snapshot direct state).finalState
    after.exitReservations = state.exitReservations ∨
      ∃ selected, after.exitReservations = state.exitReservations.push (.active .fresh incoming selected snapshot) ∧
        SavedDestinationProgress snapshot.progress := by
  cases direct with
  | true => exact Or.inr ⟨current, rfl, progress rfl⟩
  | false =>
      have frame := openExitReplacement_reservation_frame current state valid.1
      cases opened : openExitReplacement current state with
      | fault reason final =>
          exact Or.inl (by simpa only [reserveSnapshotStep, Bool.false_eq_true, ↓reduceIte,
            opened, bind, ConstructionResult.finalState] using frame.tickets)
      | ok selected final =>
          have saved := (openExitReplacement_snapshot state current selected snapshot final present opened valid.1).2.2.1
          simp only [opened, ConstructionResult.finalState] at frame
          exact Or.inr ⟨selected, by simpa only [reserveSnapshotStep, Bool.false_eq_true, ↓reduceIte,
            opened, bind, ConstructionM.get, ConstructionM.set, pure, ConstructionResult.finalState, frame.tickets], saved⟩

theorem reserveExitDestination_fresh_tickets (incoming : DestinationId) (state : ConstructionState)
    (valid : ReservationLifecycleInvariant state) :
    let after := (reserveExitDestination incoming .newValue state).finalState
    after.exitReservations = state.exitReservations ∨
      ∃ selected snapshot,
        after.exitReservations = state.exitReservations.push (.active .fresh incoming selected snapshot) ∧
          SavedDestinationProgress snapshot.progress := by
  rw [reserveExitDestination_equation]
  have freshSource : (ExitSource.newValue == ExitSource.namedResult) = false := by decide
  simp only [freshSource, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  change
    let after := ((do
      let current ← renewReceivingDestination incoming
      let before ← ConstructionM.get
      let selected ← exitFrontierAction (before.destinations.size + 1) current
      let snapshot ← lookupStep selected
      reserveSnapshotStep .fresh incoming selected snapshot
        (match snapshot.progress with | .open 0 => true | _ => false)) state).finalState
    after.exitReservations = state.exitReservations ∨
      ∃ selected snapshot,
        after.exitReservations = state.exitReservations.push (.active .fresh incoming selected snapshot) ∧
          SavedDestinationProgress snapshot.progress
  have renewalFrame := renewReceivingDestination_reservation_frame incoming state valid.1 valid.2.resumptions
  have renewalValid := renewReceivingDestination_reservation_lifecycle incoming state valid
  cases renewed : renewReceivingDestination incoming state with
  | fault reason final =>
      exact Or.inl (by simpa only [renewed, bind, ConstructionResult.finalState] using renewalFrame.tickets)
  | ok current before =>
      simp only [renewed, ConstructionResult.finalState] at renewalFrame renewalValid
      simp only [renewed, bind, ConstructionM.get]
      have frontierFrame := exitFrontierAction_finalState (before.destinations.size + 1) current before
      cases queried : exitFrontierAction (before.destinations.size + 1) current before with
      | fault reason final =>
          simp only [queried, ConstructionResult.finalState] at frontierFrame
          exact Or.inl (by simpa only [queried, bind, ConstructionResult.finalState, frontierFrame] using renewalFrame.tickets)
      | ok selected final =>
          simp only [queried, ConstructionResult.finalState] at frontierFrame
          subst final
          simp only [queried, bind, lookupStep, lookupDestination_result]
          cases found : before.destinations[selected]? with
          | none => exact Or.inl renewalFrame.tickets
          | some snapshot =>
              have extension := reserveSnapshotStep_fresh_tickets incoming selected snapshot
                (match snapshot.progress with | .open 0 => true | _ => false) before found
                (by intro direct; cases phase : snapshot.progress <;> simp_all only [phase, SavedDestinationProgress, Bool.false_eq_true]) renewalValid
              rcases extension with unchanged | ⟨chosen, updated, saved⟩
              · exact Or.inl (unchanged.trans renewalFrame.tickets)
              · exact Or.inr ⟨chosen, snapshot, by simpa only [renewalFrame.tickets] using updated, saved⟩

end Goose.Proofs.ConstructionExecutionProtocol
