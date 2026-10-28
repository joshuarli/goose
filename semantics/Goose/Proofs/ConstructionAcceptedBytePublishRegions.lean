import Goose.Proofs.ConstructionAcceptedBytePublishAnchors

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem publish_direct_packed_protection (config : EvalConfig) (initialized : Nat)
    (origin : Goose.Core.OriginId) (before after : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (fresh : ReceivingRegion) (freshMember : fresh ∈ regions) (mutable : id ∈ fresh.mutableDestinations)
    (outside : ∀ root, live root → ¬ fresh.mutableRoots root)
    (isolated : ∀ root, live root → ∀ value, before.objects.lookup root = some value → ∀ stored,
      StoredOccurrence value stored → stored.storage ≠ storageId)
    (region : ReceivingRegion) (member : region ∈ regions) (different : region.destination ≠ id)
    (present : before.construction.destinations[id]? = some row)
    (stored : before.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    ReceivingProtection config.layout after live region := by
  obtain ⟨outer, destinations, storages, successors, tickets⟩ :=
    publish_direct_packed_observed origin before after id storageId count row storage present stored progress receiver backing packed executed
  have size := publish_direct_packed_size origin before after id storageId count row storage present stored progress receiver backing packed executed
  have objects := congrArg ExecutionState.objects outer
  have ordinals := congrArg ExecutionState.objectOrdinals outer
  have old := world.protections region member
  have freshProtection := world.protections fresh freshMember
  have untouched : ∀ root, live root → ∀ value, before.objects.lookup root = some value → ∀ valueStored,
      StoredOccurrence value valueStored → valueStored.storage ≠ storageId ∧ valueStored.destination ≠ some id := by
    intro root active value found valueStored occurrence
    refine ⟨isolated root active value found valueStored occurrence, ?_⟩
    intro named
    exact freshProtection.names root active (outside root active) value found valueStored occurrence id named mutable
  refine ⟨?_, ?_, ?_, ?_, old.authority, ?_, ?_⟩
  · obtain ⟨oldRow, found⟩ := old.present
    exact ⟨oldRow, (destinations region.destination different).trans found⟩
  · constructor
    · constructor
      · intro root retained value found
        have prior : before.objects.lookup root = some value := by simpa only [objects] using found
        exact ValueStorageBacked.publish_other config.layout origin before after id storageId count row storage present stored
          progress receiver backing packed executed value (old.observations.backing.values root retained value prior)
          (untouched root retained.1 value prior)
      · intro root retained value found
        have prior : before.objects.lookup root = some (.stored value) := by simpa only [objects] using found
        simpa only [ordinals] using old.observations.backing.identities root retained value prior
    · intro root retained value found valueStored occurrence
      have prior : before.objects.lookup root = some value := by simpa only [objects] using found
      obtain ⟨unchangedStorage, unchangedDestination⟩ := untouched root retained.1 value prior valueStored occurrence
      obtain ⟨oldStorage, run, fuel, finish, storageFound, sampled, measured, lower, upper⟩ :=
        (old.observations.observations root retained value prior valueStored occurrence).observed
      have nextStorage : after.construction.storage[valueStored.storage]? = some oldStorage :=
        (storages valueStored.storage unchangedStorage).trans storageFound
      have nextDestination : ∀ target, valueStored.destination = some target →
          after.construction.destinations[target]? = before.construction.destinations[target]? := by
        intro target named
        have distinct : target ≠ id := by intro same; subst target; exact unchangedDestination named
        exact destinations target distinct
      exact ⟨oldStorage, run, fuel, finish, nextStorage,
        sampledStored_storage_transport valueStored before after oldStorage oldStorage run storageFound nextStorage rfl nextDestination sampled,
        measured, lower, upper⟩
  · intro candidate found
    exact old.cutoff candidate ((destinations region.destination different).symm.trans found)
  · intro candidate found
    exact old.landing candidate ((destinations region.destination different).symm.trans found)
  · intro target targetMember
    simpa only [size] using old.authorityBound target targetMember
  · intro root active immutable value found valueStored occurrence target named
    have prior : before.objects.lookup root = some value := by simpa only [objects] using found
    exact old.names root active immutable value prior valueStored occurrence target named

#print axioms publish_direct_packed_protection
end Goose.Proofs.ConstructionAcceptedExecution
