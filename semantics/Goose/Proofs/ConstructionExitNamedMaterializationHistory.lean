import Goose.Proofs.ConstructionExitEvaluationHistoryNamed
import Goose.Proofs.ConstructionExitCancellationHistory
import Goose.Proofs.ConstructionExecutionProtocolNamedReservationRestore
import Goose.Proofs.ConstructionExecutionProtocolNamedReservationChildren
import Goose.Proofs.ConstructionExecutionProtocolNamedReservationMaterialize
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol

local syntax "history_named_split_if" : tactic
elab_rules : tactic
  | `(tactic| history_named_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no named child condition to split"
      return [yes.mvarId, no.mvarId]

theorem namedReservationFinish_ticket_count (token incoming selected : Nat) (snapshot : PendingDestination)
    (state : ConstructionState) :
    (namedReservationFinish token incoming selected snapshot state).finalState.exitReservations.size =
      state.exitReservations.size := by
  simp only [namedReservationFinish, namedReservationReadStorage, lookupStorage_result, bind]
  cases stored : state.storage[snapshot.storage]? with
  | none => simp only [stored, ConstructionResult.finalState]
  | some storage =>
    simp only [stored]
    split
    · simp [ConstructionM.fail, ConstructionResult.finalState]
    · simp only [namedReservationWriteDestination, replaceDestination_result]
      by_cases inside : selected < state.destinations.size <;>
        simp [inside, ConstructionM.get, ConstructionM.set, ConstructionM.fail, bind, pure,
          ConstructionResult.finalState]

theorem namedReservationChildren_ticket_count (selected : Nat) (parent : PendingDestination)
    (count : Nat) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    (namedReservationChildren selected parent count state).finalState.exitReservations = state.exitReservations := by
  simp only [namedReservationChildren]
  cases progress : parent.progress <;> simp only [progress] <;> try rfl
  case built actual =>
    history_named_split_if <;> rfl
  case suspended actual expected =>
    history_named_split_if
    · rfl
    · simp only [ConstructionM.get, bind]
      cases resolved : destinationCurrent state expected with
      | error kind => rfl
      | ok current =>
        simp only [pure, bind, namedReservationReadDestination, lookupDestination_result]
        cases found : state.destinations[current]? with
        | none => rfl
        | some child =>
          simp only [found]
          history_named_split_if
          · rfl
          · have frame := abandonTree_reservation_frame current state valid
            simp only [namedReservationChildStorage, lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => rfl
            | some storage =>
              simp only [stored]
              history_named_split_if
              · rfl
              · cases backing : child.backing <;> simp only [backing]
                all_goals
                  repeat' first
                    | rfl
                    | exact frame.tickets
                    | simp only [bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                    | history_named_split_if

theorem restoreNamedDestination_ticket_count (id : Nat) (state : ConstructionState)
    (valid : ReservationLifecycleInvariant state) :
    (restoreNamedDestination id state).finalState.exitReservations.size = state.exitReservations.size := by
  let invariant : ConstructionState → Prop := fun current =>
    ReservationLifecycleInvariant current ∧ current.exitReservations.size = state.exitReservations.size
  have step : ∀ token current, invariant current → invariant (cancelExitReservation token [] current).finalState := by
    intro token current before
    exact ⟨cancelExitReservation_lifecycle token [] current before.1,
      (cancelExitReservation_ticket_count token [] current before.1).trans before.2⟩
  have initial : invariant state := ⟨valid, rfl⟩
  have all : invariant (restoreNamedDestination id state).finalState := by
    simp only [restoreNamedDestination, ConstructionM.get, bind]
    exact constructionInvariant_forEach invariant _ (fun token => cancelExitReservation token []) step state initial
  exact all.2

theorem namedReservationCommit_ticket_count (token incoming selected : Nat) (snapshot : PendingDestination)
    (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    (namedReservationCommit token incoming selected snapshot state).finalState.exitReservations.size = state.exitReservations.size := by
  simp only [namedReservationCommit, bind]
  have restoredCount := restoreNamedDestination_ticket_count selected state valid
  have restoredValid := restoreNamedDestination_lifecycle selected state valid
  cases restored : restoreNamedDestination selected state with
  | fault kind after =>
    simpa only [restored, bind, ConstructionResult.finalState] using restoredCount
  | ok ignored after =>
    cases ignored
    simp only [restored, ConstructionResult.finalState] at restoredCount restoredValid
    simp only [restored, bind, namedReservationCommit_lookup, lookupDestination_result]
    cases present : after.destinations[selected]? with
    | none => exact restoredCount
    | some parent =>
      simp only [present]
      history_named_split_if
      · exact restoredCount
      · cases snapshotProgress : snapshot.progress <;> simp only [snapshotProgress] <;> try exact restoredCount
        case built count =>
          have children := namedReservationChildren_ticket_count selected parent count after restoredValid.1
          have childrenValid := (namedReservationChildren_lifecycle selected parent count after present restoredValid).1
          cases childResult : namedReservationChildren selected parent count after with
          | fault reason finalState =>
            simp only [childResult, bind, ConstructionResult.finalState] at children ⊢
            exact (congrArg Array.size children).trans restoredCount
          | ok ignored finalState =>
            cases ignored
            simp only [childResult, ConstructionResult.finalState] at children childrenValid
            have finish := namedReservationFinish_ticket_count token incoming selected snapshot finalState
            simp only [childResult, bind]
            exact finish.trans ((congrArg Array.size children).trans restoredCount)

theorem materializeNamedReservation_ticket_count (token : Nat) (state : ConstructionState)
    (valid : ReservationLifecycleInvariant state) :
    (materializeNamedReservation token state).finalState.exitReservations.size = state.exitReservations.size := by
  rw [materializeNamedReservation_result]
  cases ticket : state.exitReservations[token]? with
  | none => rfl
  | some reservation =>
    cases reservation with
    | waiting incoming | restored | released => rfl
    | active role incoming selected snapshot =>
      cases role with
      | fresh => rfl
      | named stage =>
        cases stage with
        | awaitingSource | materialized => rfl
        | ready => exact namedReservationCommit_ticket_count token incoming selected snapshot state valid

theorem evaluationHistoryLifecycle_materialize_named (origin : Goose.Core.OriginId) (token : Nat)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient)
    (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (materializeNamedReservation token)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.materializeNamedReservation token) ambient pending
  intro state valid
  rw [materializeNamedReservation_ticket_count token state valid]
  exact Nat.le_refl _

#print axioms namedReservationCommit_ticket_count
#print axioms materializeNamedReservation_ticket_count
#print axioms evaluationHistoryLifecycle_materialize_named
#print axioms restoreNamedDestination_ticket_count
#print axioms namedReservationChildren_ticket_count
#print axioms namedReservationFinish_ticket_count

end Goose.Proofs.ConstructionAcceptedExecution
