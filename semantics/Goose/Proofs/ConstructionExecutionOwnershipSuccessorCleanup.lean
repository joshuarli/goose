import Goose.Proofs.ConstructionExecutionOwnershipSuccessorLoops
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorMutations

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

syntax "successor_cleanup" : tactic
macro_rules
| `(tactic| successor_cleanup) => `(tactic|
  first
  | exact abandonDestination_successorMap _
  | exact reserveStorage_successorMap _ _
  | exact framesSuccessorMap_of_frame _ framesSuccessors_get
  | exact framesSuccessorMap_pure _
  | exact framesSuccessorMap_fail _
  | exact writableLookup_successorMap _
  | exact framesSuccessorMap_of_frame _ (destinationLookup_successorFrame _)
  | exact framesSuccessorMap_of_frame _ (storageLookup_successorFrame _)
  | exact framesSuccessorMap_of_frame _ (destinationReplace_successorFrame _ _)
  | exact framesSuccessorMap_of_frame _ (storageReplace_successorFrame _ _)
  | exact framesSuccessorMap_of_frame _ (eventEmit_successorFrame _)
  | (apply framesSuccessorMap_listForIn; intro item value; successor_cleanup)
  | (apply framesSuccessorMap_bind
     · successor_cleanup
     · intro value; successor_cleanup)
  | (split <;> successor_cleanup))

set_option maxHeartbeats 800000 in
theorem stageDestination_successorMap (id : DestinationId) :
    FramesSuccessorMap (stageDestination id) := by
  unfold stageDestination
  apply framesSuccessorMap_bind (writableLookup id)
  · exact writableLookup_successorMap id
  · intro destination
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_cleanup

set_option maxHeartbeats 800000 in
theorem abandonTree_successorMap (id : DestinationId) :
    FramesSuccessorMap (abandonTree id) := by
  unfold abandonTree
  apply framesSuccessorMap_bind (writableLookup id)
  · exact writableLookup_successorMap id
  · intro destination
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_cleanup

end Goose.Proofs.ConstructionExecutionOwnership
