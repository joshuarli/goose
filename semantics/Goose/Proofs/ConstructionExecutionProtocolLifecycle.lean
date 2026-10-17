import Goose.Proofs.ConstructionExecutionProtocol
import Goose.Proofs.ConstructionExecutionProtocolReservationLifecycle
import Goose.Proofs.ConstructionExecutionProtocolReservationPrimitives

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

theorem runModule_destination_lifecycle_initial (fuel : Nat) (config : EvalConfig) :
    DestinationLifecycleInvariant (Goose.Proofs.Exit.stepState
      (runModule fuel config .initial)).construction := by
  letI := reservationLifecyclePrimitives
  letI := reservationLifecycleReservationPrimitives
  exact (runModule_preservesConstructionInvariant (predicate := ReservationLifecycleInvariant)
    fuel config .initial initial_reservation_lifecycle_invariant).1

theorem runModule_destination_trace_protocol (fuel : Nat) (config : EvalConfig) :
    DestinationTraceProtocol (Goose.Proofs.Exit.stepState
      (runModule fuel config .initial)).construction :=
  (runModule_destination_lifecycle_initial fuel config).1

end Goose.Proofs.ConstructionExecutionProtocol
