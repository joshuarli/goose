import Goose.Proofs.ConstructionExecutionProtocolReservationCancellation
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataTree
import Goose.Proofs.ConstructionExecutionProtocolTree
import Goose.Proofs.ConstructionExecutionProtocolCurrent
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private abbrev lookupStep (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (lookupDestination_result id state)

private abbrev replaceStep (id : DestinationId) (destination : PendingDestination) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (replaceDestination_result id destination state)

private def cancelRestoreStep (token : ExitReservationId) (reserved selected : DestinationId)
    (snapshot : PendingDestination) : ConstructionM Unit := do
  if reserved != snapshot.capability.id then
    let superseded ← lookupStep snapshot.capability.id
    match superseded.progress with
    | .exiting _ expected =>
        if expected != selected then ConstructionM.fail .ownership
    | _ => ConstructionM.fail .protocol
    replaceStep snapshot.capability.id snapshot
  else
    let state ← ConstructionM.get
    ConstructionM.set { state with destinationResumptions := (selected, snapshot) :: state.destinationResumptions }
  let state ← ConstructionM.get
  ConstructionM.set { state with exitReservations := state.exitReservations.set! token .restored }

private theorem cancelRestoreStep_preserves (state : ConstructionState) (token : ExitReservationId)
    (role : ExitReservationRole) (incoming reserved selected : DestinationId) (snapshot : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active role incoming reserved snapshot))
    (earlier : snapshot.capability.id ≤ selected) (allocated : selected < state.destinations.size)
    (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (cancelRestoreStep token reserved selected snapshot state).finalState := by
  unfold cancelRestoreStep
  by_cases replaced : reserved ≠ snapshot.capability.id
  · have replacedBool : (reserved != snapshot.capability.id) = true := bne_iff_ne.mpr replaced
    simp only [replacedBool, ↓reduceIte, lookupStep, lookupDestination_result, bind]
    cases present : state.destinations[snapshot.capability.id]? with
    | none => exact valid
    | some current =>
        simp only [present]
        cases progress : current.progress <;> try simp only [progress] <;> try exact valid
        case exiting count expected =>
          by_cases mismatch : expected ≠ selected
          · have mismatchBool : (expected != selected) = true := bne_iff_ne.mpr mismatch
            simp only [mismatchBool, ↓reduceIte, ConstructionM.fail, bind]
            exact valid
          · have mismatchBool : (expected != selected) = false := by
              have equal : expected = selected := Classical.byContradiction mismatch
              simp only [equal, bne_self_eq_false]
            simp only [mismatchBool, Bool.false_eq_true, ↓reduceIte, pure, bind, replaceStep, replaceDestination_result,
              (Array.getElem?_eq_some_iff.mp present).choose, ConstructionM.get, ConstructionM.set]
            exact reservationLifecycleInvariant_restore_ticket state token role incoming reserved snapshot current
              count expected ticket (Ne.symm replaced) present progress valid
  · have replacedBool : (reserved != snapshot.capability.id) = false := by
      have equal : reserved = snapshot.capability.id := Classical.byContradiction replaced
      simp only [equal, bne_self_eq_false]
    simp only [replacedBool, Bool.false_eq_true, ↓reduceIte, ConstructionM.get, ConstructionM.set, bind]
    exact reservationLifecycleInvariant_direct_resumption state token role incoming reserved selected snapshot
      ticket earlier allocated valid

local syntax "cancel_split_if" : tactic
elab_rules : tactic
  | `(tactic| cancel_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no cancellation condition to split"
      return [yes.mvarId, no.mvarId]

theorem cancelExitReservation_lifecycle (token : ExitReservationId) (carried : List DestinationId)
    (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (cancelExitReservation token carried state).finalState := by
  simp only [cancelExitReservation, ConstructionM.get, bind]
  cases ticket : state.exitReservations[token]? with
  | none => exact valid
  | some reservation =>
      cases reservation with
      | waiting incoming | released => exact valid
      | restored => exact valid
      | active role incoming reserved snapshot =>
          cases roleEquation : role with
          | named stage =>
              exact ⟨valid.1, destinationReservationStateValid_restore_ticket state token valid.2⟩
          | fresh =>
              simp only [roleEquation] at ticket
              simp only [ticket]
              have earlier := (valid.2.active token ExitReservationRole.fresh incoming reserved snapshot ticket).2.2.1
              cases resolved : destinationCurrent state reserved with
              | error reason => exact valid
              | ok selected =>
                  have resolvedBounds := destinationCurrent_bounds state reserved selected resolved
                  have snapshotEarlier := Nat.le_trans earlier resolvedBounds.1
                  simp only [pure, bind]
                  cancel_split_if
                  · exact valid
                  · simp only [lookupDestination_result, bind]
                    cases present : state.destinations[selected]? with
                    | none => exact valid
                    | some destination =>
                        simp only [present]
                        cancel_split_if
                        · have frame := abandonTree_reservation_frame selected state valid.1
                          have preserved : ReservationLifecycleInvariant (abandonTree selected state).finalState :=
                            ⟨abandonTree_destination_lifecycle_invariant selected state valid.1,
                              destinationReservationStateValid_frame state _ frame valid.2⟩
                          cases cleaned : abandonTree selected state with
                          | fault reason after =>
                              simpa only [cleaned, bind, ConstructionResult.finalState] using preserved
                          | ok value after =>
                              simp only [cleaned, ConstructionResult.finalState] at preserved frame
                              simp only [cleaned, bind]
                              have ticketAfter : after.exitReservations[token]? = some (.active ExitReservationRole.fresh incoming reserved snapshot) := by
                                rw [frame.tickets]
                                exact ticket
                              have expected := cancelRestoreStep_preserves after token ExitReservationRole.fresh incoming reserved selected snapshot ticketAfter
                                snapshotEarlier (Nat.lt_of_lt_of_le resolvedBounds.2 frame.destinations) preserved
                              simp only [cancelRestoreStep, lookupStep, replaceStep, lookupDestination_result,
                                replaceDestination_result, ConstructionM.get, ConstructionM.set, bind, pure] at expected ⊢
                              cases replaced : (reserved != snapshot.capability.id) <;>
                                simp only [replaced, Bool.false_eq_true, ↓reduceIte] at expected ⊢
                              · exact expected
                              · cases original : after.destinations[snapshot.capability.id]? with
                                | none => simpa only [original] using expected
                                | some row =>
                                    simp only [original] at expected ⊢
                                    cases progress : row.progress <;> simp only [progress] at expected ⊢ <;> exact expected
                        · have expected := cancelRestoreStep_preserves state token ExitReservationRole.fresh incoming reserved selected snapshot ticket
                            snapshotEarlier resolvedBounds.2 valid
                          simp only [cancelRestoreStep, lookupStep, replaceStep, lookupDestination_result,
                            replaceDestination_result, ConstructionM.get, ConstructionM.set, bind, pure] at expected ⊢
                          cases replaced : (reserved != snapshot.capability.id) <;>
                            simp only [replaced, Bool.false_eq_true, ↓reduceIte] at expected ⊢
                          · exact expected
                          · cases original : state.destinations[snapshot.capability.id]? with
                            | none => simpa only [original] using expected
                            | some row =>
                                simp only [original] at expected ⊢
                                cases progress : row.progress <;> simp only [progress] at expected ⊢ <;> exact expected

end Goose.Proofs.ConstructionExecutionProtocol
