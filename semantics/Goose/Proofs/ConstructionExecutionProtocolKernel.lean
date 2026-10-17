import Goose.Construct.Runtime
import Goose.Proofs.Exit

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct
open Goose.Core (DestinationId StorageId CopySource ConstructionRequest)

inductive ConstructionPrimitive : {α : Type} → ConstructionM α → Prop
  | reserveStorage (bytes : ByteArray) (count : Nat) : ConstructionPrimitive (reserveStorage bytes count)
  | appendStdout (bytes : ByteArray) : ConstructionPrimitive (appendStdout bytes)
  | adaptDestinationType (id : DestinationId) (logicalType : Ty) : ConstructionPrimitive (adaptDestinationType id logicalType)
  | restoreReceivingLayout (id : DestinationId) (layout : ReceivingLayout) : ConstructionPrimitive (restoreReceivingLayout id layout)
  | removeConstructionHeader (id : DestinationId) : ConstructionPrimitive (removeConstructionHeader id)
  | landExitReplacement (replacementId : DestinationId) : ConstructionPrimitive (landExitReplacement replacementId)
  | abandonPreservingExit (id replacementId : DestinationId) : ConstructionPrimitive (abandonPreservingExit id replacementId)
  | recordCopy (source : CopySource) (id : DestinationId) : ConstructionPrimitive (recordCopy source id)
  | writeElement (id : DestinationId) (bytes : ByteArray) : ConstructionPrimitive (writeElement id bytes)
  | finishDestination (id : DestinationId) : ConstructionPrimitive (finishDestination id)
  | attachChild (parentId childId : DestinationId) : ConstructionPrimitive (attachChild parentId childId)
  | attachExtension (parentId childId : DestinationId) : ConstructionPrimitive (attachExtension parentId childId)
  | attachElementExtension (parentId childId : DestinationId) : ConstructionPrimitive (attachElementExtension parentId childId)
  | publishElementDestination (id : DestinationId) : ConstructionPrimitive (publishElementDestination id)
  | retireRepeatedSource (parentId sourceId : DestinationId) : ConstructionPrimitive (retireRepeatedSource parentId sourceId)
  | truncateConstructionStorage (storageId : StorageId) (start finish count : Nat)
    (owner : Option DestinationId) (retainSlots : Bool) : ConstructionPrimitive (truncateConstructionStorage storageId start finish count owner retainSlots)
  | prepareNamedBinding (id : DestinationId) (localType : Ty) : ConstructionPrimitive (prepareNamedBinding id localType)
  | fitStagedDestination (id : DestinationId) : ConstructionPrimitive (fitStagedDestination id)
  | publishOperation (ids : List DestinationId) : ConstructionPrimitive (publishOperation ids)
  | abandonDestination (id : DestinationId) : ConstructionPrimitive (abandonDestination id)
  | stageDestination (id : DestinationId) : ConstructionPrimitive (stageDestination id)
  | abandonTree (id : DestinationId) : ConstructionPrimitive (abandonTree id)
  | adaptConstructionDestination (id : DestinationId) (producerType : Ty)
    (request : ConstructionRequest) : ConstructionPrimitive (adaptConstructionDestination id producerType request)
  | finishConstructionAdaptation (id : DestinationId) : ConstructionPrimitive (finishConstructionAdaptation id)
  | normalizeProducerDestination (id : DestinationId) (producerType : Ty) : ConstructionPrimitive (normalizeProducerDestination id producerType)
  | openDestination (storageId : StorageId) (capability : Core.Destination Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) : ConstructionPrimitive (openDestination storageId capability layout knownCount)
  | openDestinationDirect (storageId : StorageId) (capability : Core.Destination Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) : ConstructionPrimitive (openDestinationDirect storageId capability layout knownCount)
  | openChild (parentId : DestinationId) (logicalType : Ty) (layout : ReceivingLayout) : ConstructionPrimitive (openChild parentId logicalType layout)
  | openExtension (parentId : DestinationId) (request : ConstructionRequest)
    (knownCount : Option Nat) : ConstructionPrimitive (openExtension parentId request knownCount)
  | openElementExtension (parentId : DestinationId) (logicalType : Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) (receiverLoc : Core.Loc) : ConstructionPrimitive (openElementExtension parentId logicalType layout knownCount receiverLoc)
  | openExitReplacement (supersededId : DestinationId) : ConstructionPrimitive (openExitReplacement supersededId)

class ConstructionProtocolPrimitives (predicate : ConstructionState → Prop) : Prop where
  storageFrame : ∀ state storage, storage.size = state.storage.size →
    predicate state → predicate { state with storage := storage }
  preserves : ∀ {α : Type} (action : ConstructionM α), ConstructionPrimitive action →
    ∀ state, predicate state → predicate (action state).finalState

def ExecutionInvariant (predicate : ConstructionState → Prop) (state : ExecutionState) : Prop :=
  predicate state.construction

def PreservesConstructionInvariant (predicate : ConstructionState → Prop) (action : EvalM α) : Prop :=
  ∀ state, ExecutionInvariant predicate state →
    ExecutionInvariant predicate (Goose.Proofs.Exit.stepState (action state))

end Goose.Proofs.ConstructionExecutionProtocol
