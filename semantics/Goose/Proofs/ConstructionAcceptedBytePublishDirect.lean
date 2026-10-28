import Goose.Proofs.ConstructionAcceptedBytePublication
import Goose.Proofs.ConstructionRootedBackingPrefixes

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem publish_direct_packed_success (origin : Goose.Core.OriginId) (state : ExecutionState)
    (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (present : state.construction.destinations[id]? = some row)
    (stored : state.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (storageEq : row.storage = storageId)
    (packed : row.layout = .packed) (adaptation : row.adaptation = none) (fits : count < 2 ^ 32) :
    ∃ after, publishCarriers origin [.completed id] state = .ok () after := by
  have checked := preflightPublication_direct_packed state.construction id storageId count row storage
    present stored progress receiver backing storageEq packed adaptation fits
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, _root_.id, liftConstruction, publishOperation, ConstructionM.get, checked,
    List.forIn_cons, List.forIn_nil, publishReady_transition, lookupDestination_result, present, progress,
    receiver, backing, DestinationBacking.receiverStorage, lookupStorage_result, stored, packed,
    replaceStorage_result, replaceDestination_result, storageInside, inside, ↓reduceIte, emit_result]
  exact ⟨_, rfl⟩

theorem publish_direct_packed_observed (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.construction.destinations[id]? = some row)
    (stored : before.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    after = { before with construction := after.construction } ∧
    (∀ other, other ≠ id → after.construction.destinations[other]? = before.construction.destinations[other]?) ∧
    (∀ other, other ≠ storageId → after.construction.storage[other]? = before.construction.storage[other]?) ∧
    after.construction.destinationSuccessors = before.construction.destinationSuccessors ∧
    after.construction.exitReservations = before.construction.exitReservations := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, _root_.id, liftConstruction, publishOperation, ConstructionM.get, bind] at executed
  cases checked : preflightPublication before.construction [id] with
  | error reason => simp [checked, ConstructionM.fail] at executed
  | ok result =>
    cases result
    simp only [checked, List.forIn_cons, List.forIn_nil, bind, pure, publishReady_transition,
      lookupDestination_result, present, progress, receiver, backing, DestinationBacking.receiverStorage,
      lookupStorage_result, stored, packed, replaceStorage_result, replaceDestination_result,
      storageInside, inside, ↓reduceIte, emit_result, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    refine ⟨rfl, ?_, ?_, rfl, rfl⟩
    · intro other different
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm different)]
    · intro other different
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm different)]

theorem ValueStorageBacked.publish_other (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (before after : ExecutionState) (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.construction.destinations[id]? = some row)
    (stored : before.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] before = .ok () after)
    (value : Value) (valid : ValueStorageBacked layout before value)
    (outside : ∀ stored, StoredOccurrence value stored → stored.storage ≠ storageId ∧ stored.destination ≠ some id) :
    ValueStorageBacked layout after value := by
  obtain ⟨outer, destinations, storages, successors, tickets⟩ :=
    publish_direct_packed_observed origin before after id storageId count row storage present stored progress receiver backing packed executed
  induction valid with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | array values children ih =>
    refine .array values (fun child member => ih child member ?_)
    intro stored occurrence
    exact outside stored (.array values child stored member occurrence)
  | record recordId values children ih =>
    refine .record recordId values (fun child member => ih child member ?_)
    intro stored occurrence
    exact outside stored (.record recordId values child stored member occurrence)
  | stored value valid =>
    obtain ⟨otherStorage, otherDestination⟩ := outside value (.stored value)
    cases valid with
    | detached storage element storedFound detached type interval =>
      exact .stored value (.detached storage element ((storages value.storage otherStorage).trans storedFound) detached type interval)
    | named other storage destination count storedFound named binding backing type start progress element elementType interval =>
      have different : other ≠ id := by intro same; subst other; exact otherDestination named
      exact .stored value (.named other storage destination count ((storages value.storage otherStorage).trans storedFound)
        named ((destinations other different).trans binding) backing type start progress element elementType interval)

theorem AcceptedWorld.publish_direct_packed_rootedBacking (config : EvalConfig) (initialized : Nat)
    (origin : Goose.Core.OriginId) (before after : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (region : ReceivingRegion) (member : region ∈ regions) (mutable : id ∈ region.mutableDestinations)
    (outside : ∀ root, live root → ¬ region.mutableRoots root)
    (isolated : ∀ root, live root → ∀ value, before.objects.lookup root = some value → ∀ stored,
      StoredOccurrence value stored → stored.storage ≠ storageId)
    (present : before.construction.destinations[id]? = some row)
    (stored : before.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    RootedBackingState config.layout after live := by
  obtain ⟨outer, destinations, storages, successors, tickets⟩ :=
    publish_direct_packed_observed origin before after id storageId count row storage present stored progress receiver backing packed executed
  have objects := congrArg ExecutionState.objects outer
  have ordinals := congrArg ExecutionState.objectOrdinals outer
  constructor
  · intro root active value found
    have old : before.objects.lookup root = some value := by simpa only [objects] using found
    apply ValueStorageBacked.publish_other config.layout origin before after id storageId count row storage present stored
      progress receiver backing packed executed value (world.backing.values root active value old)
    intro valueStored occurrence
    refine ⟨isolated root active value old valueStored occurrence, ?_⟩
    intro named
    exact (world.protections region member).names root active (outside root active) value old valueStored occurrence id named mutable
  · intro root active value found
    have old : before.objects.lookup root = some (.stored value) := by simpa only [objects] using found
    simpa only [ordinals] using world.backing.identities root active value old

#print axioms AcceptedWorld.publish_direct_packed_rootedBacking
#print axioms ValueStorageBacked.publish_other
#print axioms publish_direct_packed_observed
#print axioms publish_direct_packed_success
end Goose.Proofs.ConstructionAcceptedExecution
