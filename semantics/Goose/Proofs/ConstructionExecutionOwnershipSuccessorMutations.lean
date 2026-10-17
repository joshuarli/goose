import Goose.Proofs.ConstructionExecutionOwnershipSuccessorMap

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

set_option maxHeartbeats 800000 in
theorem prepareNamedBinding_successorMap (id : DestinationId) (ty : Goose.Construct.Ty) :
    FramesSuccessorMap (prepareNamedBinding id ty) := by
  unfold prepareNamedBinding
  apply framesSuccessorMap_bind (writableLookup id)
  · exact writableLookup_successorMap id
  · intro destination
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_map

set_option maxHeartbeats 800000 in
theorem removeConstructionHeader_successorMap (id : DestinationId) :
    FramesSuccessorMap (removeConstructionHeader id) := by
  unfold removeConstructionHeader
  apply framesSuccessorMap_bind (writableLookup id)
  · exact writableLookup_successorMap id
  · intro destination
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_map

set_option maxHeartbeats 800000 in
theorem adaptDestinationType_successorMap (id : DestinationId) (ty : Goose.Construct.Ty) :
    FramesSuccessorMap (adaptDestinationType id ty) := by
  unfold adaptDestinationType
  apply framesSuccessorMap_bind (writableLookup id)
  · exact writableLookup_successorMap id
  · intro destination
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_map

set_option maxHeartbeats 800000 in
theorem restoreReceivingLayout_successorMap (id : DestinationId) (layout : ReceivingLayout) :
    FramesSuccessorMap (restoreReceivingLayout id layout) := by
  unfold restoreReceivingLayout
  apply framesSuccessorMap_bind (writableLookup id)
  · exact writableLookup_successorMap id
  · intro destination
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_map

set_option maxHeartbeats 800000 in
theorem adaptConstructionDestination_successorMap (id : DestinationId) (ty : Goose.Construct.Ty) (request : ConstructionRequest) :
    FramesSuccessorMap (adaptConstructionDestination id ty request) := by
  unfold adaptConstructionDestination
  apply framesSuccessorMap_bind (writableLookup id)
  · exact writableLookup_successorMap id
  · intro destination
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_map

syntax "successor_leaf" : tactic
macro_rules
| `(tactic| successor_leaf) => `(tactic|
  first
  | exact removeConstructionHeader_successorMap _
  | exact finishDestination_successorMap _
  | exact reserveStorage_successorMap _ _
  | exact appendStdout_successorMap _
  | exact framesSuccessorMap_of_frame _ framesSuccessors_get
  | exact framesSuccessorMap_pure _
  | exact framesSuccessorMap_fail _
  | exact writableLookup_successorMap _
  | exact framesSuccessorMap_of_frame _ (destinationLookup_successorFrame _)
  | exact framesSuccessorMap_of_frame _ (storageLookup_successorFrame _)
  | exact framesSuccessorMap_of_frame _ (destinationReplace_successorFrame _ _)
  | exact framesSuccessorMap_of_frame _ (storageReplace_successorFrame _ _)
  | exact framesSuccessorMap_of_frame _ (eventEmit_successorFrame _)
  | (apply framesSuccessorMap_bind
     · successor_leaf
     · intro value; successor_leaf)
  | (split <;> successor_leaf))

set_option maxHeartbeats 800000 in
theorem finishConstructionAdaptation_successorMap (id : DestinationId) :
    FramesSuccessorMap (finishConstructionAdaptation id) := by
  unfold finishConstructionAdaptation
  apply framesSuccessorMap_bind (destinationLookup id)
  · exact framesSuccessorMap_of_frame _ (destinationLookup_successorFrame id)
  · intro destination
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_leaf

set_option maxHeartbeats 800000 in
theorem fitStagedDestination_successorMap (id : DestinationId) :
    FramesSuccessorMap (fitStagedDestination id) := by
  unfold fitStagedDestination
  apply framesSuccessorMap_bind (writableLookup id)
  · exact writableLookup_successorMap id
  · intro destination
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_leaf

set_option maxHeartbeats 800000 in
theorem abandonDestination_successorMap (id : DestinationId) :
    FramesSuccessorMap (abandonDestination id) := by
  unfold abandonDestination
  apply framesSuccessorMap_bind (writableLookup id)
  · exact writableLookup_successorMap id
  · intro destination
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_leaf

set_option maxHeartbeats 800000 in
theorem truncateConstructionStorage_successorMap (storage : StorageId) (start finish count : Nat) (owner : Option DestinationId) (retain : Bool) :
    FramesSuccessorMap (truncateConstructionStorage storage start finish count owner retain) := by
  unfold truncateConstructionStorage
  apply framesSuccessorMap_bind (storageLookup storage)
  · exact framesSuccessorMap_of_frame _ (storageLookup_successorFrame storage)
  · intro destination
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_leaf

end Goose.Proofs.ConstructionExecutionOwnership
