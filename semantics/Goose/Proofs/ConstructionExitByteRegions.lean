import Goose.Proofs.ConstructionExitByteReceiverProtection
import Goose.Proofs.ConstructionExitByteAnchors

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem packed_byte_build_regions (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count : Nat) (bytes : List UInt8)
    (origin : OriginId) (before after : ExecutionState)
    (liveRoots : RootInst → Prop) (regions : List ReceivingRegion)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent before.construction id = .ok id)
    (protections : ∀ region ∈ regions, ReceivingProtection config.layout before liveRoots region)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (built : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    ∀ region ∈ regions, ReceivingProtection config.layout after liveRoots region := by
  intro region member
  by_cases selected : region.destination = id
  · exact packed_byte_build_receiver_protection fuel config environment id count bytes origin before after liveRoots region
      valid ready packed request fits current selected (protections region member) built
  · exact packed_byte_build_protection fuel config environment id count bytes origin before after liveRoots region
      valid ready packed request current selected (mutable region member) (cutoff region member) (protections region member) built

theorem packed_byte_build_accepted_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id count : Nat) (bytes : List UInt8)
    (origin : OriginId) (before after : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (liveRoots : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types liveRoots regions [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent before.construction id = .ok id)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, liveRoots root → ∃ region ∈ regions, ¬ region.mutableRoots root)
    (built : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    AcceptedWorld config initialized after ambient types liveRoots regions [] := by
  have runtime := buildExpr_bytes_runtime fuel config environment id _ bytes origin before after ready.destination count world.ownership.source current ready.present ready.opened built
  have objects := congrArg ExecutionState.objects runtime
  have ordinals := congrArg ExecutionState.objectOrdinals runtime
  have nextAct := congrArg ExecutionState.nextAct runtime
  have nextScope := congrArg ExecutionState.nextScope runtime
  have afterProtections := packed_byte_build_regions fuel config environment id count bytes origin before after liveRoots regions world.ownership.source ready packed request fits current world.protections mutable cutoff built
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
  · intro frame member
    cases member

#print axioms packed_byte_build_accepted_world

#print axioms packed_byte_build_regions

end Goose.Proofs.ConstructionAcceptedExecution
