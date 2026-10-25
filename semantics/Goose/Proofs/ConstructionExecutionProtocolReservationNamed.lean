import Goose.Proofs.ConstructionExecutionProtocolReservationCancel
import Goose.Proofs.ConstructionExecutionProtocolReservationCombinators

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem restoreNamedDestination_lifecycle (id : DestinationId) (state : ConstructionState)
    (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (restoreNamedDestination id state).finalState := by
  simp only [restoreNamedDestination, ConstructionM.get, bind]
  exact constructionInvariant_forEach ReservationLifecycleInvariant _ (fun token => cancelExitReservation token [])
    (fun token current currentValid => cancelExitReservation_lifecycle token [] current currentValid) state valid

end Goose.Proofs.ConstructionExecutionProtocol
