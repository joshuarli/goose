import Goose.Proofs.ConstructionByteLocalStopped

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem bytes_writeLoop_stopped_world_global (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation)
    (before state after : ExecutionState) (frame : FreshDestinationFrame before state) (count : Nat)
    (direct : frame.row.backing = .direct before.construction.storage.size) (opened : frame.row.progress = .open count)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (valid : OwnershipSourceState state.construction)
    (current : destinationCurrent state.construction before.construction.destinations.size =
      .ok before.construction.destinations.size) (stop : Goose.Core.Stop)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin before.construction.destinations.size (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) state = .stop stop after) :
    AcceptedWorld config initialized after ambient types live
      (freshReceivingRegion before before.construction.destinations.size :: regions) pending :=
  (bytes_writeLoop_stopped_world_with_frame bytes origin config initialized environment before state after frame count direct opened ambient types live regions pending world valid current stop executed).1

theorem bytes_finish_stopped_world_global (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation)
    (before state middle after : ExecutionState) (frame : FreshDestinationFrame before state) (count : Nat)
    (ready : OpenDestinationBacking config.layout state before.construction.destinations.size (.varr (.int .u8)) count)
    (direct : frame.row.backing = .direct before.construction.storage.size)
    (packed : frame.row.layout = .packed) (request : frame.row.capability.request = .value)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (valid : OwnershipSourceState state.construction)
    (current : destinationCurrent state.construction before.construction.destinations.size =
      .ok before.construction.destinations.size)
    (loop : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin before.construction.destinations.size (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) state = .ok PUnit.unit middle)
    (stop : Goose.Core.Stop)
    (finished : receivingAction origin before.construction.destinations.size finishDestination middle = .stop stop after) :
    AcceptedWorld config initialized after ambient types live
      (freshReceivingRegion before before.construction.destinations.size :: regions) pending :=
  (bytes_finish_stopped_world_with_frame bytes origin config initialized environment before state middle after frame count ready direct packed request ambient types live regions pending world valid current loop stop finished).1

theorem buildExpr_byteOwner_stopped_world_global (fuel : Nat) (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation) (before allocated after : ExecutionState)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (id : Nat) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before = .ok id allocated)
    (executed : buildExpr (fuel + 1) config environment id
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated = .stop stop after) :
    AcceptedWorld config initialized after ambient types live (freshReceivingRegion before id :: regions) pending :=
  (buildExpr_byteOwner_stopped_world_with_frame fuel config initialized environment before allocated after bytes origin bytesOrigin id stop ambient types live regions pending world created executed).1

theorem allocated_byteOwner_publishStop_world_global (fuel : Nat) (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation) (before allocated built after : ExecutionState)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (id : Nat) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before = .ok id allocated)
    (constructed : buildExpr (fuel + 1) config environment id
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated = .ok () built)
    (published : publishCarriers origin [.completed id] built = .stop stop after) :
    AcceptedWorld config initialized after ambient types live (freshReceivingRegion before id :: regions) pending :=
  (allocated_byteOwner_publishStop_world_with_frame fuel config initialized environment before allocated built after bytes origin bytesOrigin id stop ambient types live regions pending world created constructed published).1

theorem constructLocal_byteOwner_stopped_afterAllocation_global (fuel : Nat) (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation) (before allocated after : ExecutionState)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (id : Nat) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before = .ok id allocated)
    (executed : constructLocal ⟨config.module, environment.vars⟩ environment.act
      (.varr (.int .u8)) origin (.bytes (.varr (.int .u8)) bytes bytesOrigin)
      (fun destination => buildExpr (fuel + 1) config environment destination
        (.bytes (.varr (.int .u8)) bytes bytesOrigin)) before = .stop stop after) :
    AcceptedWorld config initialized after ambient types live (freshReceivingRegion before id :: regions) pending :=
  (constructLocal_byteOwner_stopped_afterAllocation_with_frame fuel config initialized environment before allocated after bytes origin bytesOrigin id stop ambient types live regions pending world created executed).1

#print axioms bytes_writeLoop_stopped_world_with_frame
#print axioms bytes_finish_stopped_world_with_frame
#print axioms buildExpr_byteOwner_stopped_world_with_frame
#print axioms allocated_byteOwner_publishStop_world_with_frame
#print axioms constructLocal_byteOwner_stopped_afterAllocation_with_frame

end Goose.Proofs.ConstructionAcceptedExecution
