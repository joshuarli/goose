import Goose.Proofs.ConstructionExecutionProtocolPrimitives
import Goose.Proofs.ConstructionExecutionProtocolWrites
import Goose.Proofs.ConstructionExecutionProtocolRelocation
import Goose.Proofs.ConstructionExecutionProtocolAdaptation
import Goose.Proofs.ConstructionExecutionProtocolOpen
import Goose.Proofs.ConstructionExecutionProtocolAttach
import Goose.Proofs.ConstructionExecutionProtocolPublish
import Goose.Proofs.ConstructionExecutionProtocolTree
import Goose.Proofs.ConstructionExecutionProtocolExitLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

def destinationLifecyclePrimitives : ConstructionProtocolPrimitives DestinationLifecycleInvariant where
  storageFrame := destinationLifecycleInvariant_storage_frame
  preserves := by
    intro α action primitive
    cases primitive with
    | reserveStorage bytes count => exact reserveStorage_destination_lifecycle_invariant bytes count
    | appendStdout bytes => exact appendStdout_destination_lifecycle_invariant bytes
    | adaptDestinationType id logicalType => exact adaptDestinationType_destination_lifecycle_invariant id logicalType
    | restoreReceivingLayout id layout => exact restoreReceivingLayout_destination_lifecycle_invariant id layout
    | removeConstructionHeader id => exact removeConstructionHeader_destination_lifecycle_invariant id
    | landExitReplacement replacementId => exact landExitReplacement_destination_lifecycle_invariant replacementId
    | abandonPreservingExit id replacementId => exact abandonPreservingExit_destination_lifecycle_invariant id replacementId
    | recordCopy source id => exact recordCopy_destination_lifecycle_invariant source id
    | writeElement id bytes => exact writeElement_destination_lifecycle_invariant id bytes
    | finishDestination id => exact finishDestination_destination_lifecycle_invariant id
    | attachChild parentId childId => exact attachChild_destination_lifecycle_invariant parentId childId
    | attachExtension parentId childId => exact attachExtension_destination_lifecycle_invariant parentId childId
    | attachElementExtension parentId childId => exact attachElementExtension_destination_lifecycle_invariant parentId childId
    | publishElementDestination id => exact publishElementDestination_destination_lifecycle_invariant id
    | retireRepeatedSource parentId sourceId => exact retireRepeatedSource_destination_lifecycle_invariant parentId sourceId
    | truncateConstructionStorage storageId start finish count owner retainSlots => exact truncateConstructionStorage_destination_lifecycle_invariant storageId start finish count owner retainSlots
    | prepareNamedBinding id localType => exact prepareNamedBinding_destination_lifecycle_invariant id localType
    | fitStagedDestination id => exact fitStagedDestination_destination_lifecycle_invariant id
    | publishOperation ids => exact publishOperation_destination_lifecycle_invariant ids
    | abandonDestination id => exact abandonDestination_destination_lifecycle_invariant id
    | stageDestination id => exact stageDestination_destination_lifecycle_invariant id
    | abandonTree id => exact abandonTree_destination_lifecycle_invariant id
    | adaptConstructionDestination id producerType request => exact adaptConstructionDestination_destination_lifecycle_invariant id producerType request
    | finishConstructionAdaptation id => exact finishConstructionAdaptation_destination_lifecycle_invariant id
    | normalizeProducerDestination id producerType => exact normalizeProducerDestination_destination_lifecycle_invariant id producerType
    | openDestination storageId capability layout knownCount => exact openDestination_destination_lifecycle_invariant storageId capability layout knownCount
    | openDestinationDirect storageId capability layout knownCount => exact openDestinationDirect_destination_lifecycle_invariant storageId capability layout knownCount
    | openChild parentId logicalType layout => exact openChild_destination_lifecycle_invariant parentId logicalType layout
    | openExtension parentId request knownCount => exact openExtension_destination_lifecycle_invariant parentId request knownCount
    | openElementExtension parentId logicalType layout knownCount receiverLoc => exact openElementExtension_destination_lifecycle_invariant parentId logicalType layout knownCount receiverLoc
    | openExitReplacement supersededId => exact openExitReplacement_destination_lifecycle_invariant supersededId

end Goose.Proofs.ConstructionExecutionProtocol
