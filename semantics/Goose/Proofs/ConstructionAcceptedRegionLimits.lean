import Goose.Proofs.ConstructionAcceptedAllocation
import Goose.Proofs.ConstructionAcceptedBindings
import Goose.Proofs.ConstructionAcceptedDestinationFrames

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation

def extendReceivingLimit (region : ReceivingRegion) (storage : Nat) (extent : Nat) : ReceivingRegion :=
  { region with limit := fun id => if id = storage then max (region.limit id) extent else region.limit id }

theorem ReceivingProtection.extend_unrelated_storage (layout : LayoutEnv) (state : ExecutionState)
    (live : Goose.Core.RootInst → Prop) (region : ReceivingRegion) (storage extent : Nat)
    (valid : ReceivingProtection layout state live region)
    (unrelated : ∀ row, state.construction.destinations[region.destination]? = some row → row.storage ≠ storage) :
    ReceivingProtection layout state live (extendReceivingLimit region storage extent) := by
  refine ⟨valid.present, ⟨valid.observations.backing, ?_⟩, ?_, ?_, valid.authority, valid.authorityBound, valid.names⟩
  · intro root retained value found stored occurrence
    obtain ⟨bytes, run, fuel, finish, present, sampled, measured, lower, upper⟩ :=
      (valid.observations.observations root retained value found stored occurrence).observed
    refine ⟨bytes, run, fuel, finish, present, sampled, measured, lower, ?_⟩
    change finish ≤ (if stored.storage = storage then max (region.limit stored.storage) extent else region.limit stored.storage)
    split <;> omega
  · intro row found
    have different := unrelated row found
    simpa only [extendReceivingLimit, different, ↓reduceIte] using valid.cutoff row found
  · intro row found
    have different := unrelated row found
    simpa only [extendReceivingLimit, different, ↓reduceIte] using valid.landing row found

theorem StoredValueBacking.extended_observation (layout : LayoutEnv) (state : ExecutionState)
    (region : ReceivingRegion) (stored : StoredValue) (backed : StoredValueBacking layout state stored) :
    StoredBackingObservation layout state
      (extendReceivingLimit region stored.storage (storageExtent state stored.storage)).limit stored := by
  obtain ⟨bytes, run, fuel, finish, present, sampled, measured, lower, upper⟩ :=
    (backed.observation layout state stored).observed
  refine ⟨bytes, run, fuel, finish, present, sampled, measured, lower, ?_⟩
  simp only [extendReceivingLimit, ↓reduceIte]
  exact Nat.le_trans upper (Nat.le_max_right _ _)

theorem AcceptedWorld.extend_unrelated_storage (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (storage extent : Nat)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (unrelated : ∀ region ∈ regions, ∀ row,
      state.construction.destinations[region.destination]? = some row → row.storage ≠ storage) :
    AcceptedWorld config initialized state ambient types live
      (regions.map (fun region => extendReceivingLimit region storage extent)) pending := by
  refine ⟨⟨world.ownership, world.globals, world.globalTypes, world.layouts, world.typeFrontier,
    world.syntheticFrontier, world.heap, world.objectsRegistered, world.ordinalsRegistered,
    world.backing, ?_, world.carriers⟩, world.globalLive⟩
  intro region member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact (world.protections original present).extend_unrelated_storage config.layout state live original storage extent
    (unrelated original present)

theorem newDestination_separate_from_regions (config : EvalConfig) (initialized : Nat)
    (owner : Goose.Core.ActId) (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (before after : ExecutionState) (id : Nat)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (executed : newDestination config.layout owner ty request origin none knownCount before = .ok id after) :
    ∃ destination, after.construction.destinations[id]? = some destination ∧
      destination.backing.receiverStorage = before.construction.storage.size ∧
      ∀ region ∈ regions, ∀ row, after.construction.destinations[region.destination]? = some row →
        row.storage ≠ destination.storage ∧ row.storage ≠ destination.backing.receiverStorage := by
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before after id
    world.ownership.source.structural.1.1.1 executed
  obtain ⟨destination, present, receiver, fresh⟩ :=
    newDestination_success_fresh config.layout owner ty request origin knownCount before after id executed
  refine ⟨destination, present, receiver, ?_⟩
  intro region member row found
  obtain ⟨old, oldFound⟩ := (world.protections region member).present
  have inside := (Array.getElem?_eq_some_iff.mp oldFound).1
  have current := (frame.lookup region.destination inside).trans oldFound
  have equal : row = old := Option.some.inj (found.symm.trans current)
  subst row
  have storageBound := (world.ownership.source.structural.1.1.1.2.2.1 region.destination old oldFound).1
  exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le storageBound fresh), by rw [receiver]; exact Nat.ne_of_lt storageBound⟩

theorem newDestination_excludes_old_authority (config : EvalConfig) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId) (knownCount : Option Nat)
    (before after : ExecutionState) (id : Nat) (region : ReceivingRegion)
    (bounded : ∀ previous ∈ region.mutableDestinations, previous < before.construction.destinations.size)
    (executed : newDestination config.layout owner ty request origin none knownCount before = .ok id after) :
    id ∉ region.mutableDestinations := by
  intro member
  have fresh := newDestination_fresh_id config.layout owner ty request origin knownCount before after id executed
  have prior := bounded id member
  omega

theorem newDestination_excludes_freshRegion (config : EvalConfig) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId) (knownCount : Option Nat)
    (initial before after : ExecutionState) (id regionId : Nat) (live : Goose.Core.RootInst → Prop)
    (region : ReceivingProtection config.layout before live (freshReceivingRegion initial regionId))
    (executed : newDestination config.layout owner ty request origin none knownCount before = .ok id after) :
    id ∉ (freshReceivingRegion initial regionId).mutableDestinations := by
  apply newDestination_excludes_old_authority config owner ty request origin knownCount before after id
    (freshReceivingRegion initial regionId) ?_ executed
  intro previous member
  have same : previous = regionId := by simpa only [freshReceivingRegion, List.mem_singleton] using member
  obtain ⟨row, found⟩ := region.present
  rw [same]
  exact (Array.getElem?_eq_some_iff.mp found).1

theorem bindRoot_freshStored_extendedWorld (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (root : Goose.Core.RootInst) (ty : Ty)
    (stored : StoredValue) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (compatible : RootTypeCompatible types root ty) (conforms : LayoutConforms config.layout ty)
    (represented : ValueRepresentation ty (.stored stored)) (backed : StoredValueBacking config.layout before stored)
    (fresh : before.objectOrdinals.lookup root = none)
    (unrelated : ∀ region ∈ regions, ∀ row,
      before.construction.destinations[region.destination]? = some row → row.storage ≠ stored.storage)
    (excluded : ∀ region ∈ regions, ¬ region.mutableRoots root → ∀ id,
      stored.destination = some id → id ∉ region.mutableDestinations)
    (freshType : ∀ act scope id, root = .local act scope id → act < before.nextAct ∧ scope < before.nextScope)
    (freshSynthetic : ∀ id, root = .global id → config.module.globals.size ≤ id →
      id < config.module.globals.size + before.nextScope) :
    ∃ after, bindRoot root (.stored stored) before = .ok () after ∧
      RootTypesExtend types (registerRootType types root ty) ∧
      AcceptedWorld config initialized after ambient (registerRootType types root ty)
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent before stored.storage))) pending := by
  have extended := world.extend_unrelated_storage config initialized before ambient types live regions pending
    stored.storage (storageExtent before stored.storage) unrelated
  apply bindRoot_freshStored_world config initialized before ambient types live root ty stored extended
    compatible conforms represented backed fresh ?_ freshType freshSynthetic
  intro region member immutable
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact ⟨StoredValueBacking.extended_observation config.layout before original stored backed,
    excluded original present immutable⟩

#print axioms ReceivingProtection.extend_unrelated_storage
#print axioms newDestination_separate_from_regions
#print axioms newDestination_excludes_old_authority
#print axioms newDestination_excludes_freshRegion
#print axioms bindRoot_freshStored_extendedWorld

end Goose.Proofs.ConstructionAcceptedExecution
