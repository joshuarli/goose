import Goose.Proofs.ConstructionExecutionOwnershipSuccessorMutations
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorAllocation
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorCleanup
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorExtensions
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorReceiving
import Goose.Proofs.ConstructionExecutionProtocolReservationLifecycle

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

set_option maxHeartbeats 800000 in
theorem normalizeProducerDestination_successorMap (id : DestinationId) (ty : Goose.Construct.Ty) :
    FramesSuccessorMap (normalizeProducerDestination id ty) := by
  unfold normalizeProducerDestination
  apply framesSuccessorMap_bind (writableLookup id)
  · exact writableLookup_successorMap id
  · intro destination
    cases adaptation : destination.adaptation with
    | none => simpa only [adaptation, constructionM_bind_fail] using framesSuccessorMap_fail .protocol
    | some receiving =>
        simp only [adaptation]
        cases progress : destination.progress
        all_goals simp only [progress, constructionM_bind_pure, constructionM_bind_fail]
        all_goals try exact framesSuccessorMap_fail _
        case built count =>
          generalize invalidEq : (!ty.storageType || ty.element?.isNone ||
            !ty.adaptsTo destination.capability.logicalType) = invalid
          generalize prefixEq : (match ty with
            | .varr _ => destination.capability.request == ConstructionRequest.value
            | _ => false) = producerHasHeader
          try dsimp (config := { zeta := true, zetaHave := true }) only
          successor_leaf


theorem constructionPrimitive_successorMap {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) : FramesSuccessorMap action := by
  cases primitive with
  | reserveStorage bytes count => exact reserveStorage_successorMap bytes count
  | appendStdout bytes => exact appendStdout_successorMap bytes
  | adaptDestinationType id logicalType => exact adaptDestinationType_successorMap id logicalType
  | restoreReceivingLayout id layout => exact restoreReceivingLayout_successorMap id layout
  | removeConstructionHeader id => exact removeConstructionHeader_successorMap id
  | landExitReplacement replacementId => exact framesSuccessorMap_of_frame _ (landExitReplacement_successorFrame replacementId)
  | abandonPreservingExit id replacementId => exact abandonPreservingExit_successorMap id replacementId
  | recordCopy source id => exact recordCopy_successorMap source id
  | writeElement id bytes => exact writeElement_successorMap id bytes
  | finishDestination id => exact finishDestination_successorMap id
  | attachChild parentId childId => exact attachChild_successorMap parentId childId
  | attachExtension parentId childId => exact attachExtension_successorMap parentId childId
  | attachElementExtension parentId childId => exact attachElementExtension_successorMap parentId childId
  | publishElementDestination id => exact publishElementDestination_successorMap id
  | retireRepeatedSource parentId sourceId => exact retireRepeatedSource_successorMap parentId sourceId
  | truncateConstructionStorage storageId start finish count owner retainSlots => exact truncateConstructionStorage_successorMap storageId start finish count owner retainSlots
  | prepareNamedBinding id localType => exact prepareNamedBinding_successorMap id localType
  | fitStagedDestination id => exact fitStagedDestination_successorMap id
  | publishOperation ids => exact publishOperation_successorMap ids
  | abandonDestination id => exact abandonDestination_successorMap id
  | stageDestination id => exact stageDestination_successorMap id
  | abandonTree id => exact abandonTree_successorMap id
  | adaptConstructionDestination id producerType request => exact adaptConstructionDestination_successorMap id producerType request
  | finishConstructionAdaptation id => exact finishConstructionAdaptation_successorMap id
  | normalizeProducerDestination id producerType => exact normalizeProducerDestination_successorMap id producerType
  | openDestination storageId capability layout knownCount => exact openDestination_successorMap storageId capability layout knownCount
  | openDestinationDirect storageId capability layout knownCount => exact openDestinationDirect_successorMap storageId capability layout knownCount
  | openChild parentId logicalType layout => exact openChild_successorMap parentId logicalType layout
  | openExtension parentId request knownCount => exact openExtension_successorMap parentId request knownCount
  | openElementExtension parentId logicalType layout knownCount receiverLoc => exact openElementExtension_successorMap parentId logicalType layout knownCount receiverLoc
  | openExitReplacement supersededId => exact openExitReplacement_successorMap supersededId

theorem constructionPrimitive_successors {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (lifecycle : DestinationLifecycleInvariant state) (valid : DestinationSuccessorsValid state) :
    DestinationSuccessorsValid (action state).finalState :=
  destinationSuccessorsValid_extension state _ valid
    (constructionPrimitive_successorMap action primitive state)
    (constructionPrimitive_reservation_frame action primitive state lifecycle).destinations

def successorLifecyclePrimitives : ConstructionProtocolPrimitives
    (fun state => ReservationLifecycleInvariant state ∧ DestinationSuccessorsValid state) where
  storageFrame := by
    intro state storage size valid
    exact ⟨reservationLifecyclePrimitives.storageFrame state storage size valid.1, valid.2⟩
  preserves := by
    intro α action primitive state valid
    exact ⟨reservationLifecyclePrimitives.preserves action primitive state valid.1,
      constructionPrimitive_successors action primitive state valid.1.1 valid.2⟩

end Goose.Proofs.ConstructionExecutionOwnership
