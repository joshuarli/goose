import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataWrites
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataAdaptation
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataAllocation
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataAttach
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataCleanup
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataRelocation
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataPublish
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataTree
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

theorem constructionPrimitive_reservation_frame {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (action state).finalState := by
  cases primitive with
  | reserveStorage bytes count => exact reserveStorage_reservation_frame bytes count state
  | appendStdout bytes => exact appendStdout_reservation_frame bytes state
  | adaptDestinationType id logicalType => exact adaptDestinationType_reservation_frame id logicalType state
  | restoreReceivingLayout id layout => exact restoreReceivingLayout_reservation_frame id layout state
  | removeConstructionHeader id => exact removeConstructionHeader_reservation_frame id state valid
  | landExitReplacement replacementId => exact landExitReplacement_reservation_frame replacementId state valid
  | abandonPreservingExit id replacementId => exact abandonPreservingExit_reservation_frame id replacementId state valid
  | recordCopy source id => exact recordCopy_reservation_frame source id state
  | writeElement id bytes => exact writeElement_reservation_frame id bytes state valid
  | finishDestination id => exact finishDestination_reservation_frame id state valid
  | attachChild parentId childId => exact attachChild_reservation_frame parentId childId state valid
  | attachExtension parentId childId => exact attachExtension_reservation_frame parentId childId state valid
  | attachElementExtension parentId childId => exact attachElementExtension_reservation_frame parentId childId state valid
  | publishElementDestination id => exact publishElementDestination_reservation_frame id state valid
  | retireRepeatedSource parentId sourceId => exact retireRepeatedSource_reservation_frame parentId sourceId state valid
  | truncateConstructionStorage storageId start finish count owner retainSlots => exact truncateConstructionStorage_reservation_frame storageId start finish count owner retainSlots state valid
  | prepareNamedBinding id localType => exact prepareNamedBinding_reservation_frame id localType state valid
  | fitStagedDestination id => exact fitStagedDestination_reservation_frame id state valid
  | publishOperation ids => exact publishOperation_reservation_frame ids state valid
  | abandonDestination id => exact abandonDestination_reservation_frame id state valid
  | stageDestination id => exact stageDestination_reservation_frame id state
  | abandonTree id => exact abandonTree_reservation_frame id state valid
  | adaptConstructionDestination id producerType request => exact adaptConstructionDestination_reservation_frame id producerType request state valid
  | finishConstructionAdaptation id => exact finishConstructionAdaptation_reservation_frame id state valid
  | normalizeProducerDestination id producerType => exact normalizeProducerDestination_reservation_frame id producerType state valid
  | openDestination storageId capability layout knownCount => exact openDestination_reservation_frame storageId capability layout knownCount state valid
  | openDestinationDirect storageId capability layout knownCount => exact openDestinationDirect_reservation_frame storageId capability layout knownCount state valid
  | openChild parentId logicalType layout => exact openChild_reservation_frame parentId logicalType layout state valid
  | openExtension parentId request knownCount => exact openExtension_reservation_frame parentId request knownCount state valid
  | openElementExtension parentId logicalType layout knownCount receiverLoc => exact openElementExtension_reservation_frame parentId logicalType layout knownCount receiverLoc state valid
  | openExitReplacement supersededId => exact openExitReplacement_reservation_frame supersededId state valid

#print axioms constructionPrimitive_reservation_frame

end Goose.Proofs.ConstructionExecutionProtocol
