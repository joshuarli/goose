import Goose.Proofs.ConstructionAcceptedByteChecked
import Goose.Proofs.ConstructionAcceptedRegionLimits

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem FreshDestinationFrame.bind_freshStored_world (config : EvalConfig) (initialized : Nat)
    (before evaluated : ExecutionState) (frame : FreshDestinationFrame before evaluated)
    (stored : StoredValue) (root : RootInst) (ty : Ty)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (nextWorld : AcceptedWorld config initialized evaluated ambient types live regions pending)
    (represented : ValueRepresentation ty (.stored stored)) (backed : StoredValueBacking config.layout evaluated stored)
    (identity : stored.storage = before.construction.storage.size)
    (named : stored.destination = some before.construction.destinations.size)
    (compatible : RootTypeCompatible types root ty) (conforms : LayoutConforms config.layout ty)
    (fresh : before.objectOrdinals.lookup root = none)
    (freshType : ∀ act scope id, root = .local act scope id → act < before.nextAct ∧ scope < before.nextScope)
    (freshSynthetic : ∀ id, root = .global id → config.module.globals.size ≤ id →
      id < config.module.globals.size + before.nextScope) :
    ∃ after, bindRoot root (.stored stored) evaluated = .ok () after ∧
      RootTypesExtend types (registerRootType types root ty) ∧
      AcceptedWorld config initialized after ambient (registerRootType types root ty)
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent evaluated stored.storage))) pending := by
  have ordinals := congrArg ExecutionState.objectOrdinals frame.outer
  have acts := congrArg ExecutionState.nextAct frame.outer
  have scopes := congrArg ExecutionState.nextScope frame.outer
  have unrelated : ∀ region ∈ regions, ∀ row,
      evaluated.construction.destinations[region.destination]? = some row → row.storage ≠ stored.storage := by
    intro region member row present
    obtain ⟨old, oldPresent⟩ := (world.protections region member).present
    have inside := (Array.getElem?_eq_some_iff.mp oldPresent).1
    have current := (frame.lookup region.destination inside).trans oldPresent
    have equal : row = old := Option.some.inj (present.symm.trans current)
    subst row
    have bounded := (world.ownership.source.structural.1.1.1.2.2.1 region.destination old oldPresent).1
    rw [identity]
    exact Nat.ne_of_lt bounded
  have excluded : ∀ region ∈ regions, ¬ region.mutableRoots root → ∀ id,
      stored.destination = some id → id ∉ region.mutableDestinations := by
    intro region member immutable id destination included
    have equal : before.construction.destinations.size = id := Option.some.inj (named.symm.trans destination)
    have bounded := (world.protections region member).authorityBound id included
    omega
  obtain ⟨after, bound, extended, finalWorld⟩ := bindRoot_freshStored_extendedWorld config initialized evaluated
    ambient types live root ty stored regions pending nextWorld compatible conforms
    represented backed (by simpa only [ordinals] using fresh) unrelated excluded
    (by simpa only [acts, scopes] using freshType) (by simpa only [scopes] using freshSynthetic)
  exact ⟨after, bound, extended, finalWorld⟩

theorem evalValue_byteOwner_bindWorld (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before evaluated : ExecutionState) (value : Value) (root : RootInst)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (compatible : RootTypeCompatible types root (.varr (.int .u8)))
    (conforms : LayoutConforms config.layout (.varr (.int .u8)))
    (fresh : before.objectOrdinals.lookup root = none)
    (freshType : ∀ act scope id, root = .local act scope id → act < before.nextAct ∧ scope < before.nextScope)
    (freshSynthetic : ∀ id, root = .global id → config.module.globals.size ≤ id →
      id < config.module.globals.size + before.nextScope)
    (executed : evalValue (fuel + 2) config environment (.bytes (.varr (.int .u8)) bytes origin) before =
      .ok value evaluated) :
    ∃ stored after, value = .stored stored ∧ bindRoot root value evaluated = .ok () after ∧
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config initialized after ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent evaluated stored.storage))) pending := by
  obtain ⟨nextWorld, ⟨frame⟩, stored, same, backed, identity, named, valueType⟩ :=
    evalValue_byteOwner_world fuel config initialized environment bytes origin before evaluated value ambient types live regions pending world executed
  subst value
  obtain ⟨after, bound, extended, finalWorld⟩ := frame.bind_freshStored_world config initialized before evaluated stored root
    (.varr (.int .u8)) ambient types live regions pending world nextWorld (.stored _ stored rfl valueType)
    backed identity named compatible conforms fresh freshType freshSynthetic
  exact ⟨stored, after, rfl, bound, extended, finalWorld⟩

theorem allocated_published_byteOwner_bindWorld (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before allocated built published : ExecutionState) (id : Nat) (root : RootInst)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (compatible : RootTypeCompatible types root (.varr (.int .u8)))
    (conforms : LayoutConforms config.layout (.varr (.int .u8)))
    (fresh : before.objectOrdinals.lookup root = none)
    (freshType : ∀ act scope id, root = .local act scope id → act < before.nextAct ∧ scope < before.nextScope)
    (freshSynthetic : ∀ id, root = .global id → config.module.globals.size ≤ id →
      id < config.module.globals.size + before.nextScope)
    (created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none (some bytes.length) before =
      .ok id allocated)
    (constructed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) allocated =
      .ok () built)
    (completed : publishCarriers origin [.completed id] built = .ok () published) :
    ∃ stored after, storedDestination id published = .ok stored published ∧
      bindRoot root (.stored stored) published = .ok () after ∧
      RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
      AcceptedWorld config initialized after ambient (registerRootType types root (.varr (.int .u8)))
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))) pending := by
  obtain ⟨nextWorld, ⟨frame⟩, stored, sampled, backed, identity, named, valueType⟩ :=
    allocated_published_byteOwner_world fuel config initialized environment bytes origin before allocated built published
      id ambient types live regions pending world created constructed completed
  have freshId := newDestination_fresh_id config.layout environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id created
  have named' : stored.destination = some before.construction.destinations.size := by rw [← freshId]; exact named
  obtain ⟨after, bound, extended, finalWorld⟩ := frame.bind_freshStored_world config initialized before published stored root
    (.varr (.int .u8)) ambient types live regions pending world nextWorld (.stored _ stored rfl valueType)
    backed identity named' compatible conforms fresh freshType freshSynthetic
  exact ⟨stored, after, sampled, bound, extended, finalWorld⟩

#print axioms FreshDestinationFrame.bind_freshStored_world
#print axioms evalValue_byteOwner_bindWorld
#print axioms allocated_published_byteOwner_bindWorld

end Goose.Proofs.ConstructionAcceptedExecution
