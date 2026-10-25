import Goose.Proofs.ConstructionExecutionEventPrefixReservation

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionEventPrefixProtocol
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol

def eventPrefixPrimitives (before : List Goose.Core.ConstructionEvent) : ConstructionProtocolPrimitives (PrefixInvariant before) where
  storageFrame := fun _ _ _ valid => valid
  preserves := by
    intro α action primitive state valid
    cases primitive with
    | reserveStorage bytes count => exact valid.trans (reserveStorage_events_prefix bytes count state)
    | appendStdout bytes => exact valid.trans (appendStdout_events_prefix bytes state)
    | adaptDestinationType id logicalType => exact valid.trans (adaptDestinationType_events_prefix id logicalType state)
    | restoreReceivingLayout id layout => exact valid.trans (restoreReceivingLayout_events_prefix id layout state)
    | removeConstructionHeader id => exact valid.trans (removeConstructionHeader_events_prefix id state)
    | landExitReplacement replacementId => exact valid.trans (landExitReplacement_events_prefix replacementId state)
    | abandonPreservingExit id replacementId => exact valid.trans (abandonPreservingExit_events_prefix id replacementId state)
    | recordCopy source id => exact valid.trans (recordCopy_events_prefix source id state)
    | writeElement id bytes => exact valid.trans (writeElement_events_prefix id bytes state)
    | finishDestination id => exact valid.trans (finishDestination_events_prefix id state)
    | attachChild parentId childId => exact valid.trans (attachChild_events_prefix parentId childId state)
    | attachExtension parentId childId => exact valid.trans (attachExtension_events_prefix parentId childId state)
    | attachElementExtension parentId childId => exact valid.trans (attachElementExtension_events_prefix parentId childId state)
    | publishElementDestination id => exact valid.trans (publishElementDestination_events_prefix id state)
    | retireRepeatedSource parentId sourceId => exact valid.trans (retireRepeatedSource_events_prefix parentId sourceId state)
    | truncateConstructionStorage storageId start finish count owner retainSlots => exact valid.trans (truncateConstructionStorage_events_prefix storageId start finish count owner retainSlots state)
    | prepareNamedBinding id localType => exact valid.trans (prepareNamedBinding_events_prefix id localType state)
    | fitStagedDestination id => exact valid.trans (fitStagedDestination_events_prefix id state)
    | publishOperation ids => exact valid.trans (publishOperation_events_prefix ids state)
    | abandonDestination id => exact valid.trans (abandonDestination_events_prefix id state)
    | stageDestination id => exact valid.trans (stageDestination_events_prefix id state)
    | abandonTree id => exact valid.trans (abandonTree_events_prefix id state)
    | adaptConstructionDestination id producerType request => exact valid.trans (adaptConstructionDestination_events_prefix id producerType request state)
    | finishConstructionAdaptation id => exact valid.trans (finishConstructionAdaptation_events_prefix id state)
    | normalizeProducerDestination id producerType => exact valid.trans (normalizeProducerDestination_events_prefix id producerType state)
    | openDestination storageId capability layout knownCount => exact valid.trans (openDestination_events_prefix storageId capability layout knownCount state)
    | openDestinationDirect storageId capability layout knownCount => exact valid.trans (openDestinationDirect_events_prefix storageId capability layout knownCount state)
    | openChild parentId logicalType layout => exact valid.trans (openChild_events_prefix parentId logicalType layout state)
    | openExtension parentId request knownCount => exact valid.trans (openExtension_events_prefix parentId request knownCount state)
    | openElementExtension parentId logicalType layout knownCount receiverLoc => exact valid.trans (openElementExtension_events_prefix parentId logicalType layout knownCount receiverLoc state)
    | openExitReplacement supersededId => exact valid.trans (openExitReplacement_events_prefix supersededId state)

end Goose.Proofs.ConstructionExecutionEventPrefixProtocol
