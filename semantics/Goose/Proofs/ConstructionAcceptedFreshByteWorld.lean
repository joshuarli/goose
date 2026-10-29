import Goose.Proofs.ConstructionExitByteRegions
import Goose.Proofs.ConstructionAcceptedFreshByteRegions

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem packed_byte_build_world_from_frames (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id count : Nat) (bytes : List UInt8)
    (origin : OriginId) (before after : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (liveRoots : RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types liveRoots regions pending)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (afterProtections : ∀ region ∈ regions, ReceivingProtection config.layout after liveRoots region)
    (afterCarriers : ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout after carrier)
    (covered : ∀ root, liveRoots root → ∃ region ∈ regions, ¬ region.mutableRoots root)
    (built : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    AcceptedWorld config initialized after ambient types liveRoots regions pending := by
  have runtime := buildExpr_bytes_runtime fuel config environment id _ bytes origin before after ready.destination count world.ownership.source current ready.present ready.opened built
  have objects := congrArg ExecutionState.objects runtime
  have ordinals := congrArg ExecutionState.objectOrdinals runtime
  have nextAct := congrArg ExecutionState.nextAct runtime
  have nextScope := congrArg ExecutionState.nextScope runtime
  have context := build_packed_bytes_execution_context fuel config environment id count bytes origin before after ambient world.ownership ready packed request current built
  refine ⟨⟨context, ?_, world.globalTypes, world.layouts, ?_, ?_, ?_, ?_, ?_, ?_, afterProtections, ?_⟩, world.globalLive⟩
  · refine ⟨world.globals.1, ?_⟩
    intro global bound
    obtain ⟨descriptor, value, found, stored, represented⟩ := world.globals.2 global bound
    exact ⟨descriptor, value, found, by simpa only [objects] using stored, represented⟩
  · intro act scope id ty declared
    simpa only [nextAct, nextScope] using world.typeFrontier act scope id ty declared
  · intro id ty declared outside
    simpa only [nextScope] using world.syntheticFrontier id ty declared outside
  · intro root ty value declared found
    exact world.heap root ty value declared (by simpa only [objects] using found)
  · intro root value found
    exact world.objectsRegistered root value (by simpa only [objects] using found)
  · intro root ordinal found
    exact world.ordinalsRegistered root ordinal (by simpa only [ordinals] using found)
  · constructor
    · intro root live value found
      obtain ⟨region, member, outside⟩ := covered root live
      exact (afterProtections region member).observations.backing.values root ⟨live, outside⟩ value found
    · intro root live stored found
      obtain ⟨region, member, outside⟩ := covered root live
      exact (afterProtections region member).observations.backing.identities root ⟨live, outside⟩ stored found
  · exact afterCarriers

theorem fresh_byte_build_accepted_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller producer : RuntimeActivation) (bytes : List UInt8) (allocationOrigin origin : OriginId) (knownCount : Option Nat)
    (before allocated prepared after : ExecutionState) (id : Nat) (reservation : ExitReservation)
    (ambient preparedAmbient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (fresh : ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (preparedWorld : AcceptedWorld config initialized prepared preparedAmbient types live (fresh :: regions) pending)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (construction : prepared.construction = { allocated.construction with
      exitReservations := allocated.construction.exitReservations.push reservation })
    (objects : prepared.objects = before.objects) (ordinals : prepared.objectOrdinals = before.objectOrdinals)
    (ready : OpenDestinationBacking config.layout prepared id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : bytes.length < 2 ^ 32) (selected : fresh.destination = id)
    (covered : ∀ root, live root → ∃ region ∈ fresh :: regions, ¬ region.mutableRoots root)
    (current : destinationCurrent prepared.construction id = .ok id)
    (built : buildExpr (fuel + 1) config producer id (.bytes (.varr (.int .u8)) bytes origin) prepared = .ok () after) :
    AcceptedWorld config initialized after preparedAmbient types live (fresh :: regions) pending := by
  have oldRegions := fresh_byte_build_preserves_regions fuel config initialized caller producer bytes allocationOrigin origin knownCount
    before allocated prepared after id reservation ambient types live regions pending world preparedWorld.ownership.source created construction
    objects ordinals current built
  have carriers := fresh_byte_build_preserves_pending fuel config initialized caller producer bytes allocationOrigin origin knownCount
    before allocated prepared after id reservation ambient types live regions pending world preparedWorld.ownership.source created construction current built
  have protections : ∀ region ∈ fresh :: regions, ReceivingProtection config.layout after live region := by
    intro region member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact packed_byte_build_receiver_protection fuel config producer id 0 bytes origin prepared after live region
        preparedWorld.ownership.source ready packed request (by simpa using fits) current selected
        (preparedWorld.protections region (by simp)) built
    · exact oldRegions region member
  exact packed_byte_build_world_from_frames fuel config initialized producer id 0 bytes origin prepared after preparedAmbient
    types live (fresh :: regions) pending preparedWorld ready packed request current protections carriers covered built

#print axioms fresh_byte_build_accepted_world
#print axioms packed_byte_build_world_from_frames
end Goose.Proofs.ConstructionAcceptedExecution
