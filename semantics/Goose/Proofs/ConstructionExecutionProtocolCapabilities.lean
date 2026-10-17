import Goose.Proofs.ConstructionExecutionProtocol
import Goose.Proofs.ConstructionExecutionProtocolCapabilitiesPrimitives

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

theorem destinationCapabilitiesPrimitives : ConstructionProtocolPrimitives DestinationCapabilitiesIndexed where
  storageFrame := fun _ _ _ valid => valid
  preserves := by
    intro α action primitive
    cases primitive with
    | reserveStorage bytes count => exact reserveStorage_destination_capabilities bytes count
    | appendStdout bytes => exact appendStdout_destination_capabilities bytes
    | adaptDestinationType id logicalType => exact adaptDestinationType_destination_capabilities id logicalType
    | restoreReceivingLayout id layout => exact restoreReceivingLayout_destination_capabilities id layout
    | removeConstructionHeader id => exact removeConstructionHeader_destination_capabilities id
    | landExitReplacement replacementId => exact landExitReplacement_destination_capabilities replacementId
    | abandonPreservingExit id replacementId => exact abandonPreservingExit_destination_capabilities id replacementId
    | recordCopy source id => exact recordCopy_destination_capabilities source id
    | writeElement id bytes => exact writeElement_destination_capabilities id bytes
    | finishDestination id => exact finishDestination_destination_capabilities id
    | attachChild parentId childId => exact attachChild_destination_capabilities parentId childId
    | attachExtension parentId childId => exact attachExtension_destination_capabilities parentId childId
    | attachElementExtension parentId childId => exact attachElementExtension_destination_capabilities parentId childId
    | publishElementDestination id => exact publishElementDestination_destination_capabilities id
    | retireRepeatedSource parentId sourceId => exact retireRepeatedSource_destination_capabilities parentId sourceId
    | truncateConstructionStorage storageId start finish count owner retainSlots => exact truncateConstructionStorage_destination_capabilities storageId start finish count owner retainSlots
    | prepareNamedBinding id localType => exact prepareNamedBinding_destination_capabilities id localType
    | fitStagedDestination id => exact fitStagedDestination_destination_capabilities id
    | publishOperation ids => exact publishOperation_destination_capabilities ids
    | abandonDestination id => exact abandonDestination_destination_capabilities id
    | stageDestination id => exact stageDestination_destination_capabilities id
    | abandonTree id => exact abandonTree_destination_capabilities id
    | adaptConstructionDestination id producerType request => exact adaptConstructionDestination_destination_capabilities id producerType request
    | finishConstructionAdaptation id => exact finishConstructionAdaptation_destination_capabilities id
    | normalizeProducerDestination id producerType => exact normalizeProducerDestination_destination_capabilities id producerType
    | openDestination storageId capability layout knownCount => exact openDestination_destination_capabilities storageId capability layout knownCount
    | openDestinationDirect storageId capability layout knownCount => exact openDestinationDirect_destination_capabilities storageId capability layout knownCount
    | openChild parentId logicalType layout => exact openChild_destination_capabilities parentId logicalType layout
    | openExtension parentId request knownCount => exact openExtension_destination_capabilities parentId request knownCount
    | openElementExtension parentId logicalType layout knownCount receiverLoc => exact openElementExtension_destination_capabilities parentId logicalType layout knownCount receiverLoc
    | openExitReplacement supersededId => exact openExitReplacement_destination_capabilities supersededId

theorem evaluation_destination_capabilities (fuel : Nat) (config : EvalConfig) :
    EvaluationPreservesConstructionInvariant (predicate := DestinationCapabilitiesIndexed) fuel config := by
  letI := destinationCapabilitiesPrimitives
  exact evaluation_preservesConstructionInvariant fuel config

theorem runModule_preserves_destination_capabilities (fuel : Nat) (config : EvalConfig) :
    PreservesConstructionInvariant DestinationCapabilitiesIndexed (runModule fuel config) := by
  letI := destinationCapabilitiesPrimitives
  exact runModule_preservesConstructionInvariant fuel config

theorem runModule_destination_capabilities_from_protocol (fuel : Nat) (config : EvalConfig) :
    DestinationCapabilitiesIndexed (Goose.Proofs.Exit.stepState
      (runModule fuel config .initial)).construction := by
  exact runModule_preserves_destination_capabilities fuel config .initial initial_destination_capabilities

end Goose.Proofs.ConstructionExecutionProtocol
