import Goose.Proofs.ConstructionExecutionProtocolBeginsReservation
import Goose.Proofs.ConstructionExecutionProtocolBeginsKernel
import Goose.Proofs.ConstructionExecutionProtocol

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

theorem runModule_destination_begins_from_protocol (fuel : Nat) (config : EvalConfig) :
    DestinationBegins (Goose.Proofs.Exit.stepState
      (runModule fuel config .initial)).construction := by
  letI := destinationBeginsPrimitives
  letI := destinationBeginsReservationPrimitives
  exact runModule_preservesConstructionInvariant (predicate := DestinationBegins)
    fuel config .initial initial_destination_begins

end Goose.Proofs.ConstructionExecutionProtocol
