import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataAbandon

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem reservationMetadataFrame_abandon_rows
    (action : List PendingDestination → ConstructionM Unit)
    (nilResult : ∀ state, action [] state = .ok () state)
    (consResult : ∀ destination rest state,
      action (destination :: rest) state =
        if destination.capability.id < state.destinations.size then
          action rest { state with
            destinations := state.destinations.set! destination.capability.id
              { destination with progress := .abandoned }
            events := state.events ++ [.abandon destination.capability.id] }
        else .fault .destination state)
    (rows : List PendingDestination) (state : ConstructionState) :
    ReservationMetadataFrame state (action rows state).finalState := by
  induction rows generalizing state with
  | nil => simpa only [nilResult, ConstructionResult.finalState] using ReservationMetadataFrame.refl state
  | cons destination rest ih =>
      rw [consResult]
      split
      · rename_i inside
        let before := state.destinations[destination.capability.id]
        have present : state.destinations[destination.capability.id]? = some before :=
          Array.getElem?_eq_getElem inside
        have changed : ReservationMetadataFrame state { state with
            destinations := state.destinations.set! destination.capability.id
              { destination with progress := .abandoned }
            events := state.events ++ [.abandon destination.capability.id] } := by
          apply reservationMetadataFrame_replace_terminal state destination.capability.id before _
            state.storage _ present (Nat.le_refl _)
          · trivial
          · intro count selected; simp
          · intro queried different
            simp [destinationObservations, observeDestination, Ne.symm different]
        exact changed.trans (ih _)
      · exact .refl state

theorem abandonPreservingExit_reservation_frame (id replacementId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (abandonPreservingExit id replacementId state).finalState := by
  simp only [abandonPreservingExit, ConstructionM.get, bind]
  cases checked : protectedExitDiscarded state id replacementId with
  | error fault => exact .refl state
  | ok rows =>
      exact reservationMetadataFrame_abandon_rows _ protectedAbandonment_nil_transition
        protectedAbandonment_cons_transition rows state

#print axioms reservationMetadataFrame_abandon_rows
#print axioms abandonPreservingExit_reservation_frame

end Goose.Proofs.ConstructionExecutionProtocol
