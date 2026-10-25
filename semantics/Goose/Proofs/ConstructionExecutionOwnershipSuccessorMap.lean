import Goose.Proofs.ConstructionExecutionOwnershipSuccessorRenew
import Goose.Proofs.ConstructionExecutionProtocolKernel

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

def FramesSuccessorMap (action : ConstructionM α) : Prop :=
  ∀ state, (action state).finalState.destinationSuccessors = state.destinationSuccessors

theorem framesSuccessorMap_of_frame (action : ConstructionM α) (frame : FramesSuccessors action) :
    FramesSuccessorMap action := fun state => (frame state).1

theorem framesSuccessorMap_pure (value : α) : FramesSuccessorMap (pure value : ConstructionM α) :=
  fun _ => rfl

theorem framesSuccessorMap_fail (reason : ConstructionFault) :
    FramesSuccessorMap (ConstructionM.fail reason : ConstructionM α) := fun _ => rfl

theorem framesSuccessorMap_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : FramesSuccessorMap action) (remaining : ∀ value, FramesSuccessorMap (next value)) :
    FramesSuccessorMap (action >>= next) := by
  intro state
  cases result : action state with
  | fault reason after => simpa only [bind, result, ConstructionResult.finalState] using first state
  | ok value after =>
      have before := first state
      simp only [result, ConstructionResult.finalState] at before
      simpa only [bind, result] using (remaining value after).trans before

theorem reserveStorage_successorMap (bytes : ByteArray) (count : Nat) :
    FramesSuccessorMap (reserveStorage bytes count) := fun _ => rfl

theorem appendStdout_successorMap (bytes : ByteArray) :
    FramesSuccessorMap (appendStdout bytes) := fun _ => rfl

abbrev writableLookup (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (writableDestination_result id state)

theorem writableLookup_successorMap (id : DestinationId) : FramesSuccessorMap (writableLookup id) := by
  intro state
  simp only [writableLookup, writableDestination_result]
  cases present : state.destinations[id]? with
  | none => rfl
  | some row =>
      simp only [present]
      cases destinationCanWrite state id <;> rfl

syntax "successor_map" : tactic
macro_rules
| `(tactic| successor_map) => `(tactic|
  first
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
     · successor_map
     · intro value; successor_map)
  | (split <;> successor_map))

set_option maxHeartbeats 800000 in
theorem writeElement_successorMap (id : DestinationId) (bytes : ByteArray) :
    FramesSuccessorMap (writeElement id bytes) := by
  unfold writeElement
  successor_map

set_option maxHeartbeats 800000 in
theorem finishDestination_successorMap (id : DestinationId) :
    FramesSuccessorMap (finishDestination id) := by
  unfold finishDestination
  successor_map

set_option maxHeartbeats 800000 in
theorem recordCopy_successorMap (source : CopySource) (id : DestinationId) :
    FramesSuccessorMap (recordCopy source id) := by
  unfold recordCopy
  successor_map

set_option maxHeartbeats 800000 in
theorem attachChild_successorMap (parent child : DestinationId) :
    FramesSuccessorMap (attachChild parent child) := by
  unfold attachChild
  successor_map

set_option maxHeartbeats 800000 in
theorem attachExtension_successorMap (parent child : DestinationId) :
    FramesSuccessorMap (attachExtension parent child) := by
  unfold attachExtension
  successor_map

set_option maxHeartbeats 800000 in
theorem attachElementExtension_successorMap (parent child : DestinationId) :
    FramesSuccessorMap (attachElementExtension parent child) := by
  unfold attachElementExtension
  successor_map

set_option maxHeartbeats 800000 in
theorem publishElementDestination_successorMap (id : DestinationId) :
    FramesSuccessorMap (publishElementDestination id) := by
  unfold publishElementDestination
  successor_map

set_option maxHeartbeats 800000 in
theorem retireRepeatedSource_successorMap (parent source : DestinationId) :
    FramesSuccessorMap (retireRepeatedSource parent source) := by
  unfold retireRepeatedSource
  successor_map

end Goose.Proofs.ConstructionExecutionOwnership
