import Goose.Proofs.ConstructionExitEvaluationHistoryNamed
import Goose.Proofs.ConstructionExecutionProtocolNamedReservationRestore
import Goose.Proofs.ConstructionExecutionProtocolNamedReservationChildren
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

#print axioms namedReservationChildren_ticket_count
#print axioms namedReservationFinish_ticket_count

end Goose.Proofs.ConstructionAcceptedExecution
