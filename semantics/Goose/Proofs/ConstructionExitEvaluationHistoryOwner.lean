import Goose.Proofs.ConstructionExitEvaluationHistoryReservations

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (DestinationId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

private def ticketFrameValue (state : ExecutionState) := state.construction.exitReservations

private abbrev KeepsTickets (action : EvalM α) : Prop :=
  ∀ state, ticketFrameValue (Goose.Proofs.Exit.stepState (action state)) = ticketFrameValue state

private theorem keepsTickets_query (action : EvalM α) (query : Goose.Proofs.ExitExecution.StateQuery action) : KeepsTickets action := by
  intro state
  rw [query state]

private theorem keepsTickets_bind (action : EvalM α) (next : α → EvalM β)
    (first : KeepsTickets action) (remaining : ∀ value, KeepsTickets (next value)) :
    KeepsTickets (action >>= next) :=
  Goose.Proofs.Exit.runtime_bind_frames ticketFrameValue action next first remaining

theorem restoreCompletedOwner_tickets (snapshot : PendingDestination) (incoming : DestinationId)
    (carried : List DestinationId) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState (restoreCompletedOwner snapshot incoming carried state)).construction.exitReservations =
      state.construction.exitReservations := by
  have preserve : KeepsTickets (restoreCompletedOwner snapshot incoming carried) := by
    unfold restoreCompletedOwner
    cases snapshot.progress with
    | built originalCount =>
      apply keepsTickets_bind
      · exact keepsTickets_query _ (Goose.Proofs.ExitExecution.stateQuery_receivingDestination _)
      · intro current
        apply keepsTickets_bind
        · exact keepsTickets_query _ Goose.Proofs.ExitExecution.stateQuery_get
        · intro currentState
          split
          · exact keepsTickets_query _ (Goose.Proofs.ExitExecution.stateQuery_pure _)
          · apply keepsTickets_bind
            · exact keepsTickets_query _ (Goose.Proofs.ExitExecution.stateQuery_getDestination current)
            · intro child
              apply keepsTickets_bind
              · exact keepsTickets_query _ (Goose.Proofs.ExitExecution.stateQuery_getDestination snapshot.capability.id)
              · intro parent
                cases parent.progress with
                | suspended count expected =>
                  cases child.progress with
                  | abandoned | cancelled =>
                    cases countInvalid : (count != originalCount) with
                    | true => simp [countInvalid]; exact keepsTickets_query _ (fun _ => rfl)
                    | false =>
                      cases ownerInvalid : (expected != current) with
                      | true => simp [countInvalid, ownerInvalid]; exact keepsTickets_query _ (fun _ => rfl)
                      | false =>
                        cases childInvalid : (child.use != .child snapshot.capability.id) with
                        | true => simp [countInvalid, ownerInvalid]; exact keepsTickets_query _ (fun _ => rfl)
                        | false =>
                          cases parentInvalid : ({ parent with progress := .built originalCount } != snapshot) with
                          | true => simp [countInvalid, ownerInvalid]; exact keepsTickets_query _ (fun _ => rfl)
                          | false =>
                            simp [countInvalid, ownerInvalid]
                            intro nextState
                            rfl
                  | _ => exact keepsTickets_query _ (Goose.Proofs.ExitExecution.stateQuery_pure _)
                | _ => exact keepsTickets_query _ (Goose.Proofs.ExitExecution.stateQuery_pure _)
    | _ => exact keepsTickets_query _ (fun _ => rfl)
  exact preserve state

theorem evaluationHistoryLifecycle_restore_owner (snapshot : PendingDestination) (incoming : DestinationId)
    (carried : List DestinationId) (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (restoreCompletedOwner snapshot incoming carried) ambient pending := by
  intro state valid
  have lifecycle := reservationLifecycleReservationPrimitives.restoreOwner snapshot incoming carried state valid.1
  have tickets := restoreCompletedOwner_tickets snapshot incoming carried state
  have bounded := reservationReferencesBounded_mono state.construction
    (Goose.Proofs.Exit.stepState (restoreCompletedOwner snapshot incoming carried state)).construction ambient
    (by rw [tickets]; exact Nat.le_refl _) valid.2.1
  exact ⟨lifecycle, bounded, valid.2.2⟩

#print axioms restoreCompletedOwner_tickets
#print axioms evaluationHistoryLifecycle_restore_owner

end Goose.Proofs.ConstructionAcceptedExecution
