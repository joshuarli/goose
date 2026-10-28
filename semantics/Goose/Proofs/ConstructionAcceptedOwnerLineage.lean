import Goose.Proofs.ConstructionAcceptedRegionLimits
import Goose.Proofs.ConstructionExecutionOwnershipSourcePrimitives
import Goose.Proofs.ConstructionAcceptedDestinationWorld
import Goose.Proofs.ConstructionAcceptedOpenDestination

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (ActId ConstructionRequest OriginId RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionProtocol

theorem newDestination_publishedOwner_storage (config : EvalConfig) (initialized : Nat)
    (owner : ActId) (ty : Ty) (request : ConstructionRequest) (origin : OriginId) (knownCount : Option Nat)
    (before allocated final : ExecutionState) (id count : Nat) (row : PendingDestination) (stored : StoredValue)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout owner ty request origin none knownCount before = .ok id allocated)
    (history : OwnershipSourceExtension allocated.construction final.construction)
    (present : final.construction.destinations[id]? = some row) (published : row.progress = .published count)
    (sampled : storedDestination id final = .ok stored final) :
    stored.storage = before.construction.storage.size ∧ stored.destination = some id := by
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before allocated id
    world.ownership.source.structural.1.1.1 created
  obtain ⟨original, originalPresent, receiverStorage, fresh⟩ :=
    newDestination_success_fresh config.layout owner ty request origin knownCount before allocated id created
  have idFresh := newDestination_fresh_id config.layout owner ty request origin knownCount before allocated id created
  have framePresent : allocated.construction.destinations[id]? = some frame.row := by
    rw [frame.destinations, idFresh]
    simp only [Array.getElem?_push_size]
  have same : original = frame.row := Option.some.inj (originalPresent.symm.trans framePresent)
  have receiver : original.use = .receiver := by rw [same]; exact frame.receiver
  obtain ⟨current, found, use, storage⟩ := history.receiverStorage allocated.construction final.construction id
    original originalPresent receiver
  have sameCurrent : current = row := Option.some.inj (found.symm.trans present)
  subst current
  simp only [storedDestination, getDestination, EvalM.get, present, bind, pure, published, progressCount] at sampled
  cases sampled
  exact ⟨storage.trans receiverStorage, rfl⟩

theorem buildExpr_emptyBytes_ownershipSource (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Nat) (ty : Ty) (origin : OriginId) (before after : ExecutionState) (row : PendingDestination) (count : Nat)
    (valid : DestinationLifecycleInvariant before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (present : before.construction.destinations[id]? = some row) (opened : row.progress = .open count)
    (executed : buildExpr (fuel + 1) config environment id (.bytes ty [] origin) before = .ok () after) :
    OwnershipSourceExtension before.construction after.construction ∧
      DestinationLifecycleInvariant after.construction := by
  have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  simp only [buildExpr, liftConstruction, renewal, bind, List.forIn_nil, pure, protectDestination,
    receivingAction] at executed
  cases finished : finishDestination id before.construction with
  | fault reason final => simp only [finished] at executed; cases executed
  | ok value final =>
    cases value
    simp only [finished, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    constructor
    · simpa only [finished, ConstructionResult.finalState] using
        finishDestination_ownership_source before.construction id valid
    · simpa only [finished, ConstructionResult.finalState] using
        finishDestination_destination_lifecycle_invariant id before.construction valid

theorem publishCompleted_ownershipSource (origin : OriginId) (destination : Nat) (before after : ExecutionState)
    (valid : DestinationLifecycleInvariant before.construction)
    (executed : publishCarriers origin [.completed destination] before = .ok () after) :
    OwnershipSourceExtension before.construction after.construction := by
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, id, liftConstruction] at executed
  cases result : publishOperation [destination] before.construction with
  | fault reason final => simp only [result] at executed; cases executed
  | ok value final =>
    cases value
    simp only [result, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    simpa only [result, ConstructionResult.finalState] using
      publishOperation_ownership_source [destination] before.construction valid

theorem newDestination_current_self (config : EvalConfig) (initialized : Nat) (owner : ActId) (ty : Ty)
    (request : ConstructionRequest) (origin : OriginId) (knownCount : Option Nat)
    (before after : ExecutionState) (destination : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout owner ty request origin none knownCount before = .ok destination after) :
    destinationCurrent after.construction destination = .ok destination := by
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before after destination
    world.ownership.source.structural.1.1.1 created
  have fresh := newDestination_fresh_id config.layout owner ty request origin knownCount before after destination created
  have inside : destination < after.construction.destinations.size := by
    rw [frame.destinations, Array.size_push, fresh]
    omega
  have terminal : after.construction.destinationSuccessors.lookup destination = none := by
    rw [frame.successors]
    cases found : before.construction.destinationSuccessors.lookup destination with
    | none => rfl
    | some next =>
      obtain ⟨earlier, bounded⟩ := world.ownership.source.structural.2.1 destination next found
      rw [fresh] at earlier
      exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt earlier) bounded)
  exact destinationCurrent_unaliased after.construction destination inside terminal

theorem emptyBytes_publishedOwner_storage (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (origin : OriginId) (before allocated built final : ExecutionState)
    (destination count : Nat) (row : PendingDestination) (stored : StoredValue)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none (some 0) before =
      .ok destination allocated)
    (constructed : buildExpr (fuel + 1) config environment destination (.bytes (.varr (.int .u8)) [] origin) allocated =
      .ok () built)
    (published : publishCarriers origin [.completed destination] built = .ok () final)
    (present : final.construction.destinations[destination]? = some row)
    (phase : row.progress = .published count) (sampled : storedDestination destination final = .ok stored final) :
    stored.storage = before.construction.storage.size ∧ stored.destination = some destination := by
  have allocatedWorld := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value origin (some 0)
    initialized before allocated destination ambient types live regions pending world created
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout environment.act (.varr (.int .u8)) .value origin
    (some 0) before allocated destination (.int .u8) rfl created
  have current := newDestination_current_self config initialized environment.act (.varr (.int .u8)) .value origin
    (some 0) before allocated destination ambient types live regions pending world created
  obtain ⟨buildSource, lifecycle⟩ := buildExpr_emptyBytes_ownershipSource fuel config environment destination
    (.varr (.int .u8)) origin allocated built ready.destination 0 allocatedWorld.ownership.source.structural.1.1.1
    current ready.present ready.opened constructed
  have publishSource := publishCompleted_ownershipSource origin destination built final lifecycle published
  have history := ownershipSourceExtension_trans allocated.construction built.construction final.construction buildSource publishSource
  exact newDestination_publishedOwner_storage config initialized environment.act (.varr (.int .u8)) .value origin (some 0)
    before allocated final destination count row stored ambient types live regions pending world created history present phase sampled

#print axioms newDestination_publishedOwner_storage
#print axioms buildExpr_emptyBytes_ownershipSource
#print axioms publishCompleted_ownershipSource
#print axioms newDestination_current_self
#print axioms emptyBytes_publishedOwner_storage

end Goose.Proofs.ConstructionAcceptedExecution
