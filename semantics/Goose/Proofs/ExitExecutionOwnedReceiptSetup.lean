import Goose.Proofs.ExitExecutionActiveResources
import Goose.Proofs.ConstructionExecutionProtocolReservationReserve

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol

theorem prepareExitDestination_tickets (incoming : Nat) (source : ExitSource)
    (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    (prepareExitDestinationAction incoming source state).finalState.exitReservations = state.exitReservations := by
  have renewal := renewReceivingDestination_reservation_frame incoming state valid.1 valid.2.resumptions
  have renewedValid := renewReceivingDestination_reservation_lifecycle incoming state valid
  unfold prepareExitDestinationAction
  rw [Goose.Construct.prepareExitDestination_equation]
  simp only [bind]
  cases renewed : renewReceivingDestination incoming state with
  | fault reason after => simpa only [renewed, ConstructionResult.finalState] using renewal.tickets
  | ok current middle =>
    simp only [renewed, ConstructionResult.finalState] at renewal renewedValid
    simp only [renewed, ConstructionM.get, bind]
    have finish : ∀ selected, ∀ (scanned : ConstructionState), scanned = middle →
        ((do
          let snapshot : PendingDestination ← (fun state => (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
            (lookupDestination_result selected state))
          let direct := match snapshot.progress with | .open 0 => true | _ => false
          let picked ← if direct || source == ExitSource.namedResult then pure selected else openExitReplacement selected
          pure (picked, snapshot)) scanned).finalState.exitReservations = state.exitReservations := by
      intro selected scanned same
      subst scanned
      cases present : middle.destinations[selected]? with
      | none => simp only [lookupDestination_result, present, bind, ConstructionResult.finalState]; exact renewal.tickets
      | some snapshot =>
        have opening := openExitReplacement_reservation_frame selected middle renewedValid.1
        simp only [lookupDestination_result, present, bind]
        by_cases direct : ((match snapshot.progress with | .open 0 => true | _ => false) || source == ExitSource.namedResult) = true
        · simp only [if_pos direct]
          simpa only [pure, bind, ConstructionResult.finalState] using renewal.tickets
        · simp only [if_neg direct]
          cases opened : openExitReplacement selected middle with
          | fault reason after =>
            simpa only [opened, bind, ConstructionResult.finalState] using opening.tickets.trans renewal.tickets
          | ok picked after =>
            simpa only [opened, bind, pure, ConstructionResult.finalState] using opening.tickets.trans renewal.tickets
    cases source with
    | namedResult =>
      have h := finish current middle rfl
      cases present : middle.destinations[current]? with
      | none => simpa [lookupDestination_result, present, pure, bind] using h
      | some row =>
        cases progress : row.progress <;>
          simpa [lookupDestination_result, present, progress, pure, bind] using h
    | newValue =>
      simp only [show (ExitSource.newValue == ExitSource.namedResult) = false from rfl, Bool.false_eq_true, ↓reduceIte]
      have frame := exitFrontierAction_finalState (middle.destinations.size + 1) current middle
      cases scanned : exitFrontierAction (middle.destinations.size + 1) current middle with
      | fault reason after =>
        simp only [scanned, ConstructionResult.finalState] at frame
        simpa only [scanned, bind, ConstructionResult.finalState, frame] using renewal.tickets
      | ok selected after =>
        simp only [scanned, ConstructionResult.finalState] at frame
        subst after
        have h := finish selected middle rfl
        cases present : middle.destinations[selected]? with
        | none => simpa [scanned, lookupDestination_result, present, pure, bind] using h
        | some row =>
          cases progress : row.progress <;>
            try simpa [scanned, lookupDestination_result, present, progress, pure, bind] using h
          rename_i count
          cases count <;> simpa [scanned, lookupDestination_result, present, progress, pure, bind] using h

theorem reserveExitDestination_active_push (incoming : Nat) (source : ExitSource)
    (before after : ConstructionState) (token selected : Nat)
    (valid : ReservationLifecycleInvariant before)
    (executed : reserveExitDestination incoming source before = .ok (token, selected) after) :
    token = before.exitReservations.size ∧ ∃ snapshot,
      after.exitReservations = before.exitReservations.push
        (.active (if source == ExitSource.namedResult then .named .awaitingSource else .fresh) incoming selected snapshot) := by
  have frame := prepareExitDestination_tickets incoming source before valid
  change ((do
    let (current, snapshot) ← prepareExitDestinationAction incoming source
    let state ← ConstructionM.get
    let token := state.exitReservations.size
    ConstructionM.set { state with exitReservations := (state.exitReservations.push
      (.active (if source == ExitSource.namedResult then .named .awaitingSource else .fresh) incoming current snapshot)) }
    pure (token, current)) before) = .ok (token, selected) after at executed
  simp only [bind] at executed
  cases prepared : prepareExitDestinationAction incoming source before with
  | fault reason middle => simp only [prepared] at executed; cases executed
  | ok pair middle =>
    obtain ⟨current, snapshot⟩ := pair
    simp only [prepared, ConstructionResult.finalState] at frame
    simp only [prepared, ConstructionM.get, ConstructionM.set, bind, pure] at executed
    cases executed
    exact ⟨by rw [frame], snapshot, by rw [frame]⟩

#print axioms reserveExitDestination_active_push

end Goose.Proofs.ExitExecution
