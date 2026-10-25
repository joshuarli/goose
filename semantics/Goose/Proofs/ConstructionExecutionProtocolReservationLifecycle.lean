import Goose.Proofs.ConstructionExecutionProtocolPrimitiveLifecycle
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadata

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

def reservationLifecyclePrimitives : ConstructionProtocolPrimitives ReservationLifecycleInvariant where
  storageFrame := reservationLifecycleInvariant_storage_frame
  preserves := by
    intro α action primitive state valid
    exact ⟨destinationLifecyclePrimitives.preserves action primitive state valid.1,
      destinationReservationStateValid_frame state _
        (constructionPrimitive_reservation_frame action primitive state valid.1) valid.2⟩

end Goose.Proofs.ConstructionExecutionProtocol
