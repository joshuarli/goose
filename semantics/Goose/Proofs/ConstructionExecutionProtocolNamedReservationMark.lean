import Goose.Proofs.ConstructionExecutionProtocolReservationTicketUpdates
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

local syntax "named_mark_split_if" : tactic
elab_rules : tactic
  | `(tactic| named_mark_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no named mark condition to split"
      return [yes.mvarId, no.mvarId]

private theorem mark_current_snapshot_bounds (state : ConstructionState) (selected : DestinationId)
    (source : PendingDestination) (count : Nat)
    (present : state.destinations[selected]? = some source)
    (valid : ReservationLifecycleInvariant state) :
    SavedDestinationBounds state selected { source with progress := .built count } := by
  have bounds := savedDestinationBounds_of_row state selected source present valid.1
  have correct := valid.1.2.1 selected source present
  simp only [correct] at bounds
  exact ⟨bounds.capability, bounds.allocated, bounds.writeStorage, bounds.receivingStorage, bounds.owner⟩

theorem markNamedReservation_lifecycle (token : ExitReservationId) (state : ConstructionState)
    (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (markNamedReservation token state).finalState := by
  simp only [markNamedReservation, ConstructionM.get, bind]
  cases ticket : state.exitReservations[token]? with
  | none => exact valid
  | some reservation =>
    cases reservation with
    | waiting incoming | restored | released => exact valid
    | active role incoming selected old =>
      cases role with
      | fresh => exact valid
      | named stage =>
        cases stage with
        | ready | materialized => exact valid
        | awaitingSource =>
          simp only [pure, lookupDestination_result, bind]
          cases present : state.destinations[selected]? with
          | none => exact valid
          | some source =>
            simp only [present]
            cases progress : source.progress <;> simp only [progress] <;> try exact valid
            case built count | suspended count nested | exiting count nested =>
              have update : ReservationLifecycleInvariant { state with
                  exitReservations := state.exitReservations.set! token
                    (.active (.named .ready) incoming selected {source with progress := .built count}) } := by
                constructor
                · exact valid.1
                · exact destinationReservationStateValid_replace_direct state token (.named .ready) incoming selected
                    { source with progress := .built count } (Array.getElem?_eq_some_iff.mp ticket).choose
                    (mark_current_snapshot_bounds state selected source count present valid)
                    (valid.1.2.1 selected source present) valid.2
              simp only [pure, lookupStorage_result, bind]
              cases stored : state.storage[source.storage]? with
              | none => exact valid
              | some storage =>
                simp only [stored]
                named_mark_split_if
                · exact valid
                · exact update

end Goose.Proofs.ConstructionExecutionProtocol
