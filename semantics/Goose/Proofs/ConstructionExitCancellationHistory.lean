import Goose.Proofs.ConstructionExitEvaluationHistoryReservations
import Goose.Proofs.ConstructionExecutionProtocolReservationCancel
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

private abbrev cancellationLookup (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (lookupDestination_result id state)

private abbrev cancellationReplace (id : DestinationId) (destination : PendingDestination) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (replaceDestination_result id destination state)

private def cancellationRestore (token : ExitReservationId) (reserved selected : DestinationId)
    (snapshot : PendingDestination) : ConstructionM Unit := do
  if reserved != snapshot.capability.id then
    let superseded ← cancellationLookup snapshot.capability.id
    match superseded.progress with
    | .exiting _ expected =>
      if expected != selected then ConstructionM.fail .ownership
    | _ => ConstructionM.fail .protocol
    cancellationReplace snapshot.capability.id snapshot
  else
    let state ← ConstructionM.get
    ConstructionM.set { state with destinationResumptions := (selected, snapshot) :: state.destinationResumptions }
  let state ← ConstructionM.get
  ConstructionM.set { state with exitReservations := state.exitReservations.set! token .restored }

private theorem cancellationRestore_ticket_count (state : ConstructionState) (token reserved selected : Nat)
    (snapshot : PendingDestination) :
    (cancellationRestore token reserved selected snapshot state).finalState.exitReservations.size = state.exitReservations.size := by
  unfold cancellationRestore
  by_cases replaced : reserved ≠ snapshot.capability.id
  · have different : (reserved != snapshot.capability.id) = true := bne_iff_ne.mpr replaced
    simp only [different, ↓reduceIte, cancellationLookup, lookupDestination_result, bind]
    cases present : state.destinations[snapshot.capability.id]? with
    | none => rfl
    | some current =>
      simp only [present]
      cases progress : current.progress <;> simp only [progress] <;> try rfl
      case exiting count expected =>
        by_cases mismatch : expected ≠ selected
        · have neq : (expected != selected) = true := bne_iff_ne.mpr mismatch
          simp [neq, ConstructionM.fail, bind, ConstructionResult.finalState]
        · have equal : expected = selected := Classical.byContradiction mismatch
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          simp [equal, cancellationReplace, replaceDestination_result, inside, ConstructionM.get,
            ConstructionM.set, bind, pure, ConstructionResult.finalState]
  · have equal : reserved = snapshot.capability.id := Classical.byContradiction replaced
    simp [equal, ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.finalState]

local syntax "history_cancel_split_if" : tactic
elab_rules : tactic
  | `(tactic| history_cancel_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no cancellation condition to split"
      return [yes.mvarId, no.mvarId]

theorem cancelExitReservation_ticket_count (token : ExitReservationId) (carried : List DestinationId)
    (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    (cancelExitReservation token carried state).finalState.exitReservations.size = state.exitReservations.size := by
  simp only [cancelExitReservation, ConstructionM.get, bind]
  cases ticket : state.exitReservations[token]? with
  | none => rfl
  | some reservation =>
    cases reservation with
    | waiting incoming | released | restored => rfl
    | active role incoming reserved snapshot =>
      cases roleEquation : role with
      | named stage => simp [ConstructionM.set, ConstructionResult.finalState]
      | fresh =>
        simp only [roleEquation] at ticket
        simp only [ticket]
        cases resolved : destinationCurrent state reserved with
        | error reason => rfl
        | ok selected =>
          simp only [pure, bind]
          history_cancel_split_if
          · rfl
          · simp only [lookupDestination_result, bind]
            cases present : state.destinations[selected]? with
            | none => rfl
            | some destination =>
              simp only [present]
              history_cancel_split_if
              · have frame := abandonTree_reservation_frame selected state valid.1
                cases cleaned : abandonTree selected state with
                | fault reason after =>
                  simpa only [cleaned, bind, ConstructionResult.finalState] using congrArg Array.size frame.tickets
                | ok value after =>
                  simp only [cleaned, ConstructionResult.finalState] at frame
                  simp only [cleaned, bind]
                  have expected := cancellationRestore_ticket_count after token reserved selected snapshot
                  simp only [cancellationRestore, cancellationLookup, cancellationReplace, lookupDestination_result,
                    replaceDestination_result, ConstructionM.get, ConstructionM.set, bind, pure] at expected ⊢
                  cases replaced : (reserved != snapshot.capability.id) <;>
                    simp only [replaced, Bool.false_eq_true, ↓reduceIte] at expected ⊢
                  · exact expected.trans (congrArg Array.size frame.tickets)
                  · cases original : after.destinations[snapshot.capability.id]? with
                    | none => simpa only [original] using expected.trans (congrArg Array.size frame.tickets)
                    | some row =>
                      simp only [original] at expected ⊢
                      cases progress : row.progress <;> simp only [progress] at expected ⊢ <;>
                        exact expected.trans (congrArg Array.size frame.tickets)
              · have expected := cancellationRestore_ticket_count state token reserved selected snapshot
                simp only [cancellationRestore, cancellationLookup, cancellationReplace, lookupDestination_result,
                  replaceDestination_result, ConstructionM.get, ConstructionM.set, bind, pure] at expected ⊢
                cases replaced : (reserved != snapshot.capability.id) <;>
                  simp only [replaced, Bool.false_eq_true, ↓reduceIte] at expected ⊢
                · exact expected
                · cases original : state.destinations[snapshot.capability.id]? with
                  | none => simpa only [original] using expected
                  | some row =>
                    simp only [original] at expected ⊢
                    cases progress : row.progress <;> simp only [progress] at expected ⊢ <;> exact expected

theorem evaluationHistoryLifecycle_cancel (origin : OriginId) (token : Nat) (carried : List DestinationId)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (cancelExitReservation token carried)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.cancelExitReservation token carried) ambient pending
  intro state valid
  rw [cancelExitReservation_ticket_count token carried state valid]
  exact Nat.le_refl _

#print axioms cancelExitReservation_ticket_count
#print axioms evaluationHistoryLifecycle_cancel

end Goose.Proofs.ConstructionAcceptedExecution
