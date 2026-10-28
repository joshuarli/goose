import Goose.Proofs.ConstructionAcceptedBytePublishRegions

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem AcceptedWorld.publish_direct_packed (config : EvalConfig) (initialized : Nat)
    (origin : Goose.Core.OriginId) (before after : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (fresh : ReceivingRegion)
    (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (world : AcceptedWorld config initialized before (.returned [.completed id] :: ambient) types live [fresh]
      [⟨[.construct id], [.completed id]⟩])
    (noTickets : ∀ frame ∈ ambient, frame.tickets = [])
    (mutable : id ∈ fresh.mutableDestinations) (outside : ∀ root, live root → ¬ fresh.mutableRoots root)
    (isolated : ∀ root, live root → ∀ value, before.objects.lookup root = some value → ∀ stored,
      StoredOccurrence value stored → stored.storage ≠ storageId)
    (present : before.construction.destinations[id]? = some row)
    (stored : before.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    AcceptedWorld config initialized after ambient types live [] [] := by
  obtain ⟨outer, destinations, storages, successors, tickets⟩ :=
    publish_direct_packed_observed origin before after id storageId count row storage present stored progress receiver backing packed executed
  have objects := congrArg ExecutionState.objects outer
  have ordinals := congrArg ExecutionState.objectOrdinals outer
  have acts := congrArg ExecutionState.nextAct outer
  have scopes := congrArg ExecutionState.nextScope outer
  have ownership := publish_direct_packed_context origin before after ambient id storageId count row storage
    world.ownership noTickets present stored progress receiver backing packed executed
  have rooted := world.publish_direct_packed_rootedBacking config initialized origin before after
    (.returned [.completed id] :: ambient) types live [fresh] [⟨[.construct id], [.completed id]⟩] id storageId count row storage
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
    cases member
  · intro frame member
    cases member

#print axioms AcceptedWorld.publish_direct_packed
end Goose.Proofs.ConstructionAcceptedExecution
