import Goose.Proofs.ConstructionByteStorageWorld
import Goose.Proofs.ConstructionAcceptedByteChecked
import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumps
import Goose.Proofs.ExitExecutionInvocationProducersEscapeSupport

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionDelivery
open Goose.Proofs.ExitExecution

theorem newDestination_byteOwner_world_outcome (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (owner : Goose.Core.ActId) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) :
    match newDestination config.layout owner (.varr (.int .u8)) .value origin none knownCount before with
    | .ok id after =>
        AcceptedWorld config frame.initialized after ambient types live (freshReceivingRegion before id :: regions) pending ∧
        AcceptedFrame config accepted frame after types
    | .stop _ after => AcceptedWorld config frame.initialized after ambient types live regions pending ∧
        AcceptedFrame config accepted frame after types
    | _ => False := by
  cases step : newDestination config.layout owner (.varr (.int .u8)) .value origin none knownCount before with
  | escape address carriers after =>
    exact False.elim (producerNeverEscapes_newDestination config.layout owner (.varr (.int .u8)) .value origin none knownCount
      before address carriers after step)
  | jump target kind after =>
    exact False.elim (neverJumps_newDestination config.layout owner (.varr (.int .u8)) .value origin none knownCount
      before target kind after step)
  | stop reason after =>
    exact ⟨newDestination_byteOwner_stopped_world_any config frame.initialized owner origin knownCount before after reason
      ambient types live regions pending world step,
      newDestination_byteOwner_stopped_frame_any owner origin knownCount reason source step⟩
  | ok id after =>
    obtain ⟨fresh⟩ := newDestination_fresh_frame config.layout owner (.varr (.int .u8)) .value origin knownCount
      before after id world.ownership.source.structural.1.1.1 step
    exact ⟨newDestination_acceptedWorld config owner (.varr (.int .u8)) .value origin knownCount frame.initialized
      before after id ambient types live regions pending world step, fresh.acceptedFrame source⟩

#print axioms newDestination_byteOwner_world_outcome
end Goose.Proofs.ConstructionAcceptedExecution
