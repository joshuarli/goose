import Goose.Proofs.ConstructionByteStorageContext
import Goose.Proofs.ConstructionByteStorageCarriers

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem reserveByteStorage_world (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types live regions pending) :
    AcceptedWorld config initialized (reserveByteStorage state) ambient types live regions pending := by
  refine ⟨⟨reserveByteStorage_context state ambient world.ownership, world.globals, world.globalTypes, world.layouts,
    world.typeFrontier, world.syntheticFrontier, world.heap, world.objectsRegistered, world.ordinalsRegistered,
    reserveByteStorage_rooted_backing state config.layout live world.backing, ?_, ?_⟩, world.globalLive⟩
  · intro region member
    exact reserveByteStorage_protection state config.layout live region (world.protections region member)
  · intro carrierFrame member
    obtain ⟨ready, backed⟩ := world.carriers carrierFrame member
    exact ⟨reserveByteStorage_carriers_ready state carrierFrame.channels carrierFrame.carriers ready,
      fun carrier present => reserveByteStorage_carrier_backing state config.layout carrier (backed carrier present)⟩

theorem newDestination_byteOwner_stopped_world_any (config : EvalConfig) (initialized : Nat)
    (owner : Goose.Core.ActId) (origin : Goose.Core.OriginId) (knownCount : Option Nat) (before after : ExecutionState)
    (stop : Goose.Core.Stop) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (executed : newDestination config.layout owner (.varr (.int .u8)) .value origin none knownCount before = .stop stop after) :
    AcceptedWorld config initialized after ambient types live regions pending := by
  have same := newDestination_byteOwner_stopped_state_any config.layout owner origin knownCount before after stop executed
  change after = reserveByteStorage before at same
  subst after
  exact reserveByteStorage_world config initialized before ambient types live regions pending world


theorem newDestination_byteOwner_stopped_world (config : EvalConfig) (initialized : Nat)
    (owner : Goose.Core.ActId) (origin : Goose.Core.OriginId) (count : Nat) (before after : ExecutionState)
    (stop : Goose.Core.Stop) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (executed : newDestination config.layout owner (.varr (.int .u8)) .value origin none (some count) before = .stop stop after) :
    AcceptedWorld config initialized after ambient types live regions pending := by
  exact newDestination_byteOwner_stopped_world_any config initialized owner origin (some count) before after stop
    ambient types live regions pending world executed

#print axioms reserveByteStorage_world
#print axioms newDestination_byteOwner_stopped_world
#print axioms newDestination_byteOwner_stopped_world_any

end Goose.Proofs.ConstructionAcceptedExecution
