import Goose.Proofs.ConstructionAcceptedFreshBytePublishPending

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem fresh_byte_publish_accepted_world (config : EvalConfig) (initialized : Nat)
    (origin : Goose.Core.OriginId) (before after : ExecutionState) (ambient : OwnershipAmbient)
    (initial : ExecutionState) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (sourceWorld : AcceptedWorld config initialized initial ambient types live regions pending)
    (world : AcceptedWorld config initialized before (.returned [.completed id] :: ambient) types live
      (freshReceivingRegion initial id :: regions) (⟨[.construct id], [.completed id]⟩ :: pending))
    (freshId : id = initial.construction.destinations.size) (freshStorage : storageId = initial.construction.storage.size)
    (frame : FreshDestinationFrame { before with construction := { initial.construction with
      exitReservations := initial.construction.exitReservations.push .released } } before)
    (isolated : ∀ root, live root → ∀ value, before.objects.lookup root = some value → ∀ stored,
      StoredOccurrence value stored → stored.storage ≠ storageId)
    (present : before.construction.destinations[id]? = some row)
    (stored : before.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    AcceptedWorld config initialized after ambient types live regions pending := by
  obtain ⟨outer, destinations, storages, successors, tickets⟩ :=
    publish_direct_packed_observed origin before after id storageId count row storage present stored progress receiver backing packed executed
  have objects := congrArg ExecutionState.objects outer
  have ordinals := congrArg ExecutionState.objectOrdinals outer
  have acts := congrArg ExecutionState.nextAct outer
  have scopes := congrArg ExecutionState.nextScope outer
  have ownership := publish_direct_packed_context_general origin before after ambient id storageId count row storage
    world.ownership present stored progress receiver backing packed executed
  let fresh := freshReceivingRegion initial id
  have mutable : id ∈ fresh.mutableDestinations := by simp [fresh, freshReceivingRegion]
  have outside : ∀ root, live root → ¬ fresh.mutableRoots root := by simp [fresh, freshReceivingRegion]
  have rooted := world.publish_direct_packed_rootedBacking config initialized origin before after
    (.returned [.completed id] :: ambient) types live (fresh :: regions) (⟨[.construct id], [.completed id]⟩ :: pending) id storageId count row storage
    fresh (by simp) mutable outside isolated present stored progress receiver backing packed executed
  refine ⟨⟨ownership, ?_, world.globalTypes, world.layouts, ?_, ?_, ?_, ?_, ?_, rooted, ?_, ?_⟩, world.globalLive⟩
  · refine ⟨world.globals.1, ?_⟩
    intro global bound
    obtain ⟨descriptor, value, found, representedAt, represented⟩ := world.globals.2 global bound
    exact ⟨descriptor, value, found, by simpa only [objects] using representedAt, represented⟩
  · intro act scope localId ty declared
    simpa only [acts, scopes] using world.typeFrontier act scope localId ty declared
  · intro global ty declared outsideGlobal
    simpa only [scopes] using world.syntheticFrontier global ty declared outsideGlobal
  · intro root ty value declared found
    exact world.heap root ty value declared (by simpa only [objects] using found)
  · intro root value found
    exact world.objectsRegistered root value (by simpa only [objects] using found)
  · intro root ordinal found
    exact world.ordinalsRegistered root ordinal (by simpa only [ordinals] using found)
  · intro region member
    have old := sourceWorld.protections region member
    have different : region.destination ≠ id := by
      have bounded := old.authorityBound region.destination old.authority
      rw [freshId]
      omega
    exact publish_direct_packed_protection config initialized origin before after (.returned [.completed id] :: ambient)
      types live (fresh :: regions) (⟨[.construct id], [.completed id]⟩ :: pending) id storageId count row storage world
      fresh (by simp) mutable outside isolated region (by simp [member]) different present stored progress receiver backing packed executed
  · exact fresh_byte_publish_preserves_pending config initialized origin initial before after ambient types live regions pending id count row
      sourceWorld freshId frame present (by simpa only [freshStorage] using backing) progress packed executed

#print axioms fresh_byte_publish_accepted_world
end Goose.Proofs.ConstructionAcceptedExecution
