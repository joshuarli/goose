import Goose.Proofs.ConstructionExecutionProtocolExecutionKernel

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

inductive ConstructionReservationPrimitive : {α : Type} → ConstructionM α → Prop
  | reserveExitDestination (incoming : DestinationId) (source : ExitSource) :
      ConstructionReservationPrimitive (reserveExitDestination incoming source)
  | waitExitDestination (incoming : DestinationId) :
      ConstructionReservationPrimitive (waitExitDestination incoming)
  | selectWaitingExitDestination (token : ExitReservationId) (source : ExitSource) :
      ConstructionReservationPrimitive (selectWaitingExitDestination token source)
  | rearmExitReservation (borrowed : BorrowedWaitingExitReservation) :
      ConstructionReservationPrimitive (rearmExitReservation borrowed)
  | markNamedReservation (token : ExitReservationId) :
      ConstructionReservationPrimitive (markNamedReservation token)
  | materializeNamedReservation (token : ExitReservationId) :
      ConstructionReservationPrimitive (materializeNamedReservation token)
  | renewReceivingDestination (incoming : DestinationId) :
      ConstructionReservationPrimitive (renewReceivingDestination incoming)
  | releaseExitReservation (token : ExitReservationId) :
      ConstructionReservationPrimitive (releaseExitReservation token)
  | cancelExitReservation (token : ExitReservationId) (carried : List DestinationId) :
      ConstructionReservationPrimitive (cancelExitReservation token carried)
  | landExitReplacementChain (id : DestinationId) :
      ConstructionReservationPrimitive (landExitReplacementChain id)
  | landExitReplacementInto (receiving id : DestinationId) :
      ConstructionReservationPrimitive (landExitReplacementInto receiving id)

class ConstructionReservationPrimitives (predicate : ConstructionState → Prop) : Prop where
  restoreOwner : ∀ (snapshot : PendingDestination) (incoming : DestinationId) (carried : List DestinationId),
    PreservesConstructionInvariant predicate (restoreCompletedOwner snapshot incoming carried)
  preserves : ∀ {α : Type} (action : ConstructionM α), ConstructionReservationPrimitive action →
    ∀ state, predicate state → predicate (action state).finalState

end Goose.Proofs.ConstructionExecutionProtocol
