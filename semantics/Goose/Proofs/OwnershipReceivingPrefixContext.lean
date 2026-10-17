import Goose.Construct.Runtime

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Core (DestinationId)

inductive OwnershipReceivingCapture
  | destination (incoming : DestinationId)
  | ownerExtension (snapshot : PendingDestination) (incoming : DestinationId) (capturedStorage : ReceivingStorage)

def OwnershipReceivingCapture.incoming : OwnershipReceivingCapture → DestinationId
  | .destination incoming | .ownerExtension _ incoming _ => incoming

end Goose.Proofs.ConstructionExecutionOwnership
