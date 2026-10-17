import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataUpdates
import Goose.Proofs.ConstructionExecutionProtocolTree

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem abandonDestination_reservation_frame (id : DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (abandonDestination id state).finalState := by
  simp only [abandonDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have storageInside := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> try simp only [progress] <;> try exact .refl state
          all_goals
            simp only [lookupStorage_result, bind]
            cases state.storage[destination.storage]? <;>
              simp only [bind, replaceStorage_result, replaceDestination_result, storageInside,
                inside, ↓reduceIte, emit_result, ConstructionResult.finalState]
            · exact .refl state
            · apply reservationMetadataFrame_replace_terminal state id destination _ _ _ present
              · simp
              · trivial
              · intro count selected; simp
              · intro queried different
                simp [destinationObservations, observeDestination, Ne.symm different]

end Goose.Proofs.ConstructionExecutionProtocol
