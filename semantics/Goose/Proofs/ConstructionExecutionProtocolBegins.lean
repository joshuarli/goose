import Goose.Proofs.ConstructionExecutionProtocol

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

def destinationBeginsPrimitives : ConstructionProtocolPrimitives DestinationBegins where
  storageFrame := fun _ _ _ valid => valid
  preserves := by
    intro α action primitive
    cases primitive with
    | reserveStorage bytes count => exact FramesDestinationBegins.preserves _ (reserveStorage_destination_begins_frame bytes count)
    | appendStdout bytes => exact FramesDestinationBegins.preserves _ (appendStdout_destination_begins_frame bytes)
    | adaptDestinationType id logicalType => exact FramesDestinationBegins.preserves _ (adaptDestinationType_destination_begins_frame id logicalType)
    | restoreReceivingLayout id layout => exact FramesDestinationBegins.preserves _ (restoreReceivingLayout_destination_begins_frame id layout)
    | removeConstructionHeader id => exact FramesDestinationBegins.preserves _ (removeConstructionHeader_destination_begins_frame id)
    | landExitReplacement replacementId => exact FramesDestinationBegins.preserves _ (landExitReplacement_destination_begins_frame replacementId)
    | abandonPreservingExit id replacementId => exact FramesDestinationBegins.preserves _ (abandonPreservingExit_destination_begins_frame id replacementId)
    | recordCopy source id => exact FramesDestinationBegins.preserves _ (recordCopy_destination_begins_frame source id)
    | writeElement id bytes => exact FramesDestinationBegins.preserves _ (writeElement_destination_begins_frame id bytes)
    | finishDestination id => exact FramesDestinationBegins.preserves _ (finishDestination_destination_begins_frame id)
    | attachChild parentId childId => exact FramesDestinationBegins.preserves _ (attachChild_destination_begins_frame parentId childId)
    | attachExtension parentId childId => exact FramesDestinationBegins.preserves _ (attachExtension_destination_begins_frame parentId childId)
    | attachElementExtension parentId childId => exact FramesDestinationBegins.preserves _ (attachElementExtension_destination_begins_frame parentId childId)
    | publishElementDestination id => exact FramesDestinationBegins.preserves _ (publishElementDestination_destination_begins_frame id)
    | retireRepeatedSource parentId sourceId => exact FramesDestinationBegins.preserves _ (retireRepeatedSource_destination_begins_frame parentId sourceId)
    | truncateConstructionStorage storageId start finish count owner retainSlots => exact FramesDestinationBegins.preserves _ (truncateConstructionStorage_destination_begins_frame storageId start finish count owner retainSlots)
    | prepareNamedBinding id localType => exact FramesDestinationBegins.preserves _ (prepareNamedBinding_destination_begins_frame id localType)
    | fitStagedDestination id => exact FramesDestinationBegins.preserves _ (fitStagedDestination_destination_begins_frame id)
    | publishOperation ids => exact FramesDestinationBegins.preserves _ (publishOperation_destination_begins_frame ids)
    | abandonDestination id => exact FramesDestinationBegins.preserves _ (abandonDestination_destination_begins_frame id)
    | stageDestination id => exact FramesDestinationBegins.preserves _ (stageDestination_destination_begins_frame id)
    | abandonTree id => exact FramesDestinationBegins.preserves _ (abandonTree_destination_begins_frame id)
    | adaptConstructionDestination id producerType request => exact FramesDestinationBegins.preserves _ (adaptConstructionDestination_destination_begins_frame id producerType request)
    | finishConstructionAdaptation id => exact FramesDestinationBegins.preserves _ (finishConstructionAdaptation_destination_begins_frame id)
    | normalizeProducerDestination id producerType => exact FramesDestinationBegins.preserves _ (normalizeProducerDestination_destination_begins_frame id producerType)
    | openDestination storageId capability layout knownCount => exact openDestination_destination_begins storageId capability layout knownCount
    | openDestinationDirect storageId capability layout knownCount => exact openDestinationDirect_destination_begins storageId capability layout knownCount
    | openChild parentId logicalType layout => exact openChild_destination_begins parentId logicalType layout
    | openExtension parentId request knownCount => exact openExtension_destination_begins parentId request knownCount
    | openElementExtension parentId logicalType layout knownCount receiverLoc => exact openElementExtension_destination_begins parentId logicalType layout knownCount receiverLoc
    | openExitReplacement supersededId => exact openExitReplacement_destination_begins supersededId

theorem runModule_destination_begins_from_protocol (fuel : Nat) (config : EvalConfig) :
    DestinationBegins (Goose.Proofs.Exit.stepState
      (runModule fuel config .initial)).construction := by
  letI := destinationBeginsPrimitives
  exact runModule_preservesConstructionInvariant (predicate := DestinationBegins)
    fuel config .initial initial_destination_begins

end Goose.Proofs.ConstructionExecutionProtocol
