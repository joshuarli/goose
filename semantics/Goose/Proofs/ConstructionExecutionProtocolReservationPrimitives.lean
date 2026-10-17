import Goose.Proofs.ConstructionExecutionProtocolReservationRearm
import Goose.Proofs.ConstructionExecutionProtocolReservationReserve
import Goose.Proofs.ConstructionExecutionProtocolReservationLandingMetadata
import Goose.Proofs.ConstructionExecutionProtocolReservationKernel
import Goose.Proofs.ConstructionExecutionProtocolReservationOwnerRuntime
import Goose.Proofs.ConstructionExecutionProtocolNamedReservation

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

def reservationLifecycleReservationPrimitives : ConstructionReservationPrimitives ReservationLifecycleInvariant where
  restoreOwner := restoreCompletedOwner_reservation_lifecycle
  preserves := by
    intro α action primitive state valid
    cases primitive with
    | reserveExitDestination incoming source =>
        exact reserveExitDestination_reservation_lifecycle incoming source state valid
    | waitExitDestination incoming => exact waitExitDestination_reservation_lifecycle incoming state valid
    | selectWaitingExitDestination token source => exact selectWaitingExitDestination_reservation_lifecycle token source state valid
    | rearmExitReservation borrowed => exact rearmExitReservation_lifecycle borrowed state valid
    | markNamedReservation token => exact markNamedReservation_lifecycle token state valid
    | materializeNamedReservation token => exact materializeNamedReservation_lifecycle token state valid
    | renewReceivingDestination incoming =>
        exact renewReceivingDestination_reservation_lifecycle incoming state valid
    | releaseExitReservation token => exact releaseExitReservation_lifecycle state token valid
    | cancelExitReservation token carried => exact cancelExitReservation_lifecycle token carried state valid
    | landExitReplacementChain id => exact landExitReplacementChain_reservation_lifecycle id state valid
    | landExitReplacementInto receiving id => exact landExitReplacementInto_reservation_lifecycle receiving id state valid

end Goose.Proofs.ConstructionExecutionProtocol
