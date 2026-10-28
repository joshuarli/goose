import Goose.Proofs.ConstructionAcceptedAllocation
import Goose.Proofs.ConstructionExecutionOwnershipSourceAllocation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (DestinationId)
open Goose.Proofs.ExitExecution
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership

private theorem prefix_lookup (before after : Array α) (prefixEq : after.extract 0 before.size = before)
    (id : Nat) (row : α) (present : before[id]? = some row) : after[id]? = some row := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have size := congrArg Array.size prefixEq
  simp only [Array.size_extract, Nat.sub_zero] at size
  have bound : id < min before.size after.size := by omega
  have found := congrArg (fun rows => rows[id]?) prefixEq
  simpa only [Array.getElem?_extract, Nat.sub_zero, Nat.zero_add, bound, ↓reduceIte] using found.trans present

structure FreshDestinationFrame (before after : ExecutionState) where
  outer : after = { before with construction := after.construction }
  row : PendingDestination
  destinations : after.construction.destinations = before.construction.destinations.push row
  receiver : row.use = .receiver
  successors : after.construction.destinationSuccessors = before.construction.destinationSuccessors
  tickets : after.construction.exitReservations = before.construction.exitReservations
  storage : ∀ (id : Nat) (storage : ReceivingStorage), before.construction.storage[id]? = some storage → after.construction.storage[id]? = some storage

private theorem openDestination_tickets (state after : ConstructionState) (target : Nat)
    (capability : Goose.Core.Destination Ty) (layout : ReceivingLayout) (knownCount : Option Nat) (id : Nat)
    (valid : DestinationLifecycleInvariant state)
    (executed : openDestination target capability layout knownCount state = .ok id after) :
    after.exitReservations = state.exitReservations := by
  have frame := openDestination_reservation_frame target capability layout knownCount state valid
  simpa only [executed, ConstructionResult.finalState] using frame.tickets

private theorem destination_prefix_push (before after : Array α) (id : Nat) (row : α)
    (prefixEq : after.extract 0 before.size = before) (fresh : id = before.size)
    (size : after.size = before.size + 1) (present : after[id]? = some row) : after = before.push row := by
  apply Array.ext_getElem?
  intro index
  by_cases old : index < before.size
  · have beforeFound : before[index]? = some before[index] := Array.getElem?_eq_some_iff.mpr ⟨old, rfl⟩
    have afterFound := prefix_lookup before after prefixEq index before[index] beforeFound
    rw [afterFound]
    simp only [Array.getElem?_push, Nat.ne_of_lt old, ↓reduceIte, beforeFound]
  · by_cases last : index = before.size
    · subst index
      simpa only [fresh, Array.getElem?_push_size] using present
    · have outside : after.size ≤ index := by omega
      rw [Array.getElem?_eq_none_iff.mpr outside]
      exact (Array.getElem?_eq_none_iff.mpr (by simpa only [Array.size_push, ← size] using outside)).symm

theorem newDestination_fresh_frame (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (before after : ExecutionState) (id : Nat)
    (valid : DestinationLifecycleInvariant before.construction)
    (executed : newDestination layout owner ty request origin none knownCount before = .ok id after) :
    Nonempty (FreshDestinationFrame before after) := by
  let prepared : ExecutionState := { before with construction :=
    { before.construction with storage := before.construction.storage.push ⟨ByteArray.empty, 0⟩ } }
  have query := Goose.Proofs.ConstructionExecutionProtocol.stateQuery_receivingLayout layout ty prepared
  have existing : ∀ source original, before.construction.storage[source]? = some original →
      AllocationObservation before after source := by
    intro source original present
    simpa only [executed, Goose.Proofs.Exit.stepState] using
      newDestination_existing_source layout owner ty request origin knownCount before source original present
  have preparedValid : DestinationLifecycleInvariant prepared.construction := by
    exact reserveStorage_destination_lifecycle_invariant ByteArray.empty 0 before.construction valid
  simp only [newDestination, liftConstruction, reserveStorage, ConstructionM.get, ConstructionM.set, bind, pure] at executed
  change ((receivingLayout layout ty >>= fun selected => liftConstruction origin
    (openDestination before.construction.storage.size
      ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount)) prepared) = .ok id after at executed
  cases result : receivingLayout layout ty prepared with
  | stop reason middle | escape target carriers middle | jump target kind middle =>
    simp only [bind, result] at executed
    cases executed
  | ok selected middle =>
    simp only [result, Goose.Proofs.Exit.stepState] at query
    subst middle
    simp only [bind, result, liftConstruction] at executed
    cases opened : openDestination before.construction.storage.size
        ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount prepared.construction with
    | fault reason final => simp only [opened] at executed; cases executed
    | ok value final =>
      simp only [opened] at executed
      cases executed
      obtain ⟨fresh, successors, size, row, present, receiver⟩ := openDestination_receiver_row prepared.construction final _ _ _ _ id opened
      have destinationsPrefix : final.destinations.extract 0 before.construction.destinations.size = before.construction.destinations := by
        by_cases empty : before.construction.destinations.size = 0
        · have nil : before.construction.destinations = #[] := Array.size_eq_zero_iff.mp empty
          rw [nil]
          exact Array.extract_eq_empty_of_le (by simp)
        · have inside : 0 < before.construction.destinations.size := Nat.pos_of_ne_zero empty
          let original := before.construction.destinations[0]
          have originalFound : before.construction.destinations[0]? = some original := Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
          have storageInside := (valid.2.2.1 0 original originalFound).1
          let storage := before.construction.storage[original.storage]
          have stored : before.construction.storage[original.storage]? = some storage := Array.getElem?_eq_some_iff.mpr ⟨storageInside, rfl⟩
          exact (existing original.storage storage stored).2.2.1
      refine ⟨⟨rfl, row, destination_prefix_push _ _ id row destinationsPrefix fresh size present, receiver, successors,
        openDestination_tickets prepared.construction final _ _ selected knownCount id preparedValid opened, ?_⟩⟩
      intro source original found
      exact (existing source original found).2.2.2.trans found

theorem FreshDestinationFrame.lookup {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (id : Nat) (inside : id < before.construction.destinations.size) :
    after.construction.destinations[id]? = before.construction.destinations[id]? := by
  rw [frame.destinations]
  simp only [Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte]

theorem FreshDestinationFrame.size {before after : ExecutionState} (frame : FreshDestinationFrame before after) :
    before.construction.destinations.size ≤ after.construction.destinations.size := by
  simp only [frame.destinations, Array.size_push]
  omega

theorem FreshDestinationFrame.observation {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (source : Nat) (storage : ReceivingStorage) (present : before.construction.storage[source]? = some storage) :
    AllocationObservation before after source := by
  have objects := congrArg ExecutionState.objects frame.outer
  have ordinals := congrArg ExecutionState.objectOrdinals frame.outer
  refine ⟨objects, ordinals, ?_, ?_⟩
  · rw [frame.destinations]
    exact (Array.extract_push_of_le (Nat.le_refl _)).trans (Array.extract_size ..)
  · exact (frame.storage source storage present).trans present.symm

theorem FreshDestinationFrame.stored_backing {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (layout : LayoutEnv) (stored : StoredValue) (backed : StoredValueBacking layout before stored) :
    StoredValueBacking layout after stored := by
  obtain ⟨storage, run, present, sampled, interval⟩ := backed.sampled layout before stored
  exact backed.allocation_frame layout before after stored (frame.observation stored.storage storage present)

theorem FreshDestinationFrame.stored_observation {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (layout : LayoutEnv) (limit : Nat → Nat) (stored : StoredValue)
    (backed : StoredValueBacking layout before stored) (observed : StoredBackingObservation layout before limit stored) :
    StoredBackingObservation layout after limit stored := by
  obtain ⟨storage, run, fuel, finish, present, sampled, measured, lower, upper⟩ := observed.observed
  have next := frame.storage stored.storage storage present
  have sampledAfter := sampledStored_storage_transport stored before after storage storage run present next rfl
    (fun id named => frame.lookup id (backed.named_bound layout before stored id named)) sampled
  exact ⟨storage, run, fuel, finish, next, sampledAfter, measured, lower, upper⟩

theorem FreshDestinationFrame.value_backing {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (layout : LayoutEnv) (value : Value) (backed : ValueStorageBacked layout before value) :
    ValueStorageBacked layout after value := by
  induction backed with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | array values children ih => exact .array values ih
  | record id values children ih => exact .record id values ih
  | stored stored backing => exact .stored stored (frame.stored_backing layout stored backing)

theorem FreshDestinationFrame.rooted_observations {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (layout : LayoutEnv) (live : Goose.Core.RootInst → Prop) (limit : Nat → Nat)
    (valid : RootedBackingObservations layout before live limit) : RootedBackingObservations layout after live limit := by
  have objects := congrArg ExecutionState.objects frame.outer
  have ordinals := congrArg ExecutionState.objectOrdinals frame.outer
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro root kept value found
    rw [objects] at found
    exact frame.value_backing layout value (valid.backing.values root kept value found)
  · intro root kept stored found
    rw [objects] at found
    rw [ordinals]
    exact valid.backing.identities root kept stored found
  · intro root kept value found stored occurrence
    rw [objects] at found
    exact frame.stored_observation layout limit stored
      ((valid.backing.values root kept value found).occurrence_backing layout before value stored occurrence)
      (valid.observations root kept value found stored occurrence)

theorem FreshDestinationFrame.protection {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (layout : LayoutEnv) (live : Goose.Core.RootInst → Prop) (region : ReceivingRegion)
    (valid : ReceivingProtection layout before live region) : ReceivingProtection layout after live region := by
  obtain ⟨row, present⟩ := valid.present
  have found := (frame.lookup region.destination (Array.getElem?_eq_some_iff.mp present).1).trans present
  have objects := congrArg ExecutionState.objects frame.outer
  refine ⟨⟨row, found⟩, frame.rooted_observations layout _ region.limit valid.observations, ?_, ?_, valid.authority, ?_, ?_⟩
  · intro actual actualFound
    have same : actual = row := Option.some.inj (actualFound.symm.trans found)
    subst actual
    exact valid.cutoff row present
  · intro actual actualFound
    have same : actual = row := Option.some.inj (actualFound.symm.trans found)
    subst actual
    exact valid.landing row present
  · intro id member
    exact Nat.lt_of_lt_of_le (valid.authorityBound id member) frame.size
  · intro root kept outside value valueFound stored occurrence id named
    exact valid.names root kept outside value (by rw [objects] at valueFound; exact valueFound) stored occurrence id named

private theorem FreshDestinationFrame.stored_query {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (id : Nat) (row : PendingDestination) (stored : StoredValue)
    (present : before.construction.destinations[id]? = some row)
    (sampled : storedDestination id before = .ok stored before) : storedDestination id after = .ok stored after := by
  have found := (frame.lookup id (Array.getElem?_eq_some_iff.mp present).1).trans present
  simp only [storedDestination, getDestination, EvalM.get, present, found, bind, pure] at sampled ⊢
  cases count : progressCount row.progress with
  | none => simp only [count, fault, EvalM.stop] at sampled; cases sampled
  | some count =>
    simp only [count] at sampled ⊢
    cases sampled
    rfl

theorem FreshDestinationFrame.carrier_backing {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (layout : LayoutEnv) (carrier : Carrier) (valid : CarrierResultBacking layout before carrier) :
    CarrierResultBacking layout after carrier := by
  cases valid with
  | register value backed => exact .register value (frame.value_backing layout value backed)
  | completed id count row stored present built sampled backed =>
    exact .completed id count row stored ((frame.lookup id (Array.getElem?_eq_some_iff.mp present).1).trans present) built
      (frame.stored_query id row stored present sampled) (frame.stored_backing layout stored backed)
  | pendingNamed token incoming selected count snapshot source stored ticket present marked phase sampled backed =>
    exact .pendingNamed token incoming selected count snapshot source stored
      (by simpa only [frame.tickets] using ticket)
      ((frame.lookup selected (Array.getElem?_eq_some_iff.mp present).1).trans present) marked phase
      (frame.stored_query selected source stored present sampled) (frame.stored_backing layout stored backed)

private theorem FreshDestinationFrame.parent_ready {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (id : Nat) (row : PendingDestination) (valid : LandingParentReady before.construction id row) :
    LandingParentReady after.construction id row := by
  cases valid with
  | receiver use => exact .receiver use
  | child parent count owner use present progress =>
    exact .child parent count owner use ((frame.lookup parent (Array.getElem?_eq_some_iff.mp present).1).trans present) progress
  | replacement parent count owner use present progress =>
    exact .replacement parent count owner use ((frame.lookup parent (Array.getElem?_eq_some_iff.mp present).1).trans present) progress

private theorem FreshDestinationFrame.replacement_path {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (receiving source : Nat) (path : OwnershipReplacementPath before.construction.destinations receiving source) :
    OwnershipReplacementPath after.construction.destinations receiving source := by
  induction path with
  | refl => exact .refl _
  | step id parent ancestor row present use tail ih =>
    exact .step id parent ancestor row ((frame.lookup id (Array.getElem?_eq_some_iff.mp present).1).trans present) use ih

def FreshDestinationFrame.receiving_ready {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (incoming source : Nat) (valid : ReceivingCarrierLandingReady before incoming source) :
    ReceivingCarrierLandingReady after incoming source := by
  exact ⟨valid.receiving, valid.sourceDestination, valid.receivingDestination,
    destinationCurrent_extension before.construction after.construction frame.successors frame.size incoming valid.receiving valid.resolved,
    (frame.lookup source (Array.getElem?_eq_some_iff.mp valid.sourcePresent).1).trans valid.sourcePresent,
    (frame.lookup valid.receiving (Array.getElem?_eq_some_iff.mp valid.receivingPresent).1).trans valid.receivingPresent,
    frame.replacement_path valid.receiving source valid.path, frame.parent_ready valid.receiving valid.receivingDestination valid.parent,
    valid.ordered⟩

theorem FreshDestinationFrame.carrier_ready {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (channel : Channel) (carrier : Carrier) (valid : CarrierLandingReady before channel carrier) :
    CarrierLandingReady after channel carrier := by
  cases valid with
  | register ty value => exact .register ty value
  | construct incoming source ready => exact .construct incoming source (frame.receiving_ready incoming source ready)
  | completion token incoming selected source role snapshot ticket ready =>
    exact .completion token incoming selected source role snapshot (by simpa only [frame.tickets] using ticket)
      (frame.receiving_ready selected source ready)
  | pendingNamed token incoming selected snapshot ticket =>
    exact .pendingNamed token incoming selected snapshot (by simpa only [frame.tickets] using ticket)

theorem FreshDestinationFrame.carriers_ready {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (channels : List Channel) (carriers : List Carrier) (valid : CarriersLandingReady before channels carriers) :
    CarriersLandingReady after channels carriers :=
  ⟨valid.lengths, fun channel carrier member => frame.carrier_ready channel carrier (valid.pairs channel carrier member)⟩

#print axioms newDestination_fresh_frame
#print axioms FreshDestinationFrame.protection
#print axioms FreshDestinationFrame.carrier_backing
#print axioms FreshDestinationFrame.carriers_ready

end Goose.Proofs.ConstructionAcceptedExecution
