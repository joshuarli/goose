import Goose.Proofs.ConstructionRootedBackingPrefixes
import Lean.Elab.Tactic.Split
import Init.Data.Array.Extract

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct
open Goose.Core (DestinationId StorageId)

local syntax "allocation_split_if" : tactic
elab_rules : tactic
  | `(tactic| allocation_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.SplitIf.splitIfAt? goal (← goal.getType) none
        | Lean.throwError "no allocation condition"
      return [yes.mvarId, no.mvarId]

local syntax "allocation_split_if_at " ident : tactic
elab_rules : tactic
  | `(tactic| allocation_split_if_at $name:ident) => do
      let hypothesis ← Lean.Elab.Tactic.getFVarId name
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.SplitIf.splitIfAt? goal (← Lean.Meta.inferType (.fvar hypothesis)) none
          | Lean.throwError "no allocation hypothesis condition"
        return [yes.mvarId, no.mvarId]

def AllocationObservation (before after : ExecutionState) (source : StorageId) : Prop :=
  after.objects = before.objects ∧ after.objectOrdinals = before.objectOrdinals ∧
    after.construction.destinations.extract 0 before.construction.destinations.size =
      before.construction.destinations ∧
    after.construction.storage[source]? = before.construction.storage[source]?

private theorem lookup_preserved_by_prefix (before after : Array α)
    (preserved : after.extract 0 before.size = before) (index : Nat) (value : α)
    (present : before[index]? = some value) : after[index]? = some value := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have size := congrArg Array.size preserved
  simp only [Array.size_extract, Nat.sub_zero] at size
  have bound : index < min before.size after.size := by omega
  have found := congrArg (fun values => values[index]?) preserved
  simpa only [Array.getElem?_extract, Nat.sub_zero, Nat.zero_add, bound, ↓reduceIte] using found.trans present

theorem StoredValueBacking.allocation_frame (layout : LayoutEnv) (before after : ExecutionState)
    (stored : StoredValue) (backed : StoredValueBacking layout before stored)
    (frame : AllocationObservation before after stored.storage) :
    StoredValueBacking layout after stored := by
  cases backed with
  | detached storage element present detached type interval =>
      exact .detached storage element (frame.2.2.2.trans present) detached type interval
  | named id storage destination count present named binding backing type start progress element elementType interval =>
      exact .named id storage destination count (frame.2.2.2.trans present) named
        (lookup_preserved_by_prefix _ _ frame.2.2.1 id destination binding)
        backing type start progress element elementType interval

set_option maxHeartbeats 8000000 in
theorem openDestination_existing_source (state : ConstructionState)
    (target sourceStorage : StorageId)
    (capability : Goose.Core.Destination Ty) (layout : ReceivingLayout) (knownCount : Option Nat)
    (storage : ReceivingStorage)
    (storageFound : state.storage[sourceStorage]? = some storage)
    (different : sourceStorage ≠ target) :
    ((openDestination target capability layout knownCount state).finalState.destinations.extract 0 state.destinations.size,
      (openDestination target capability layout knownCount state).finalState.storage[sourceStorage]?) =
        (state.destinations, some storage) := by
  have storageInside := (Array.getElem?_eq_some_iff.mp storageFound).1
  have storageNotLast := Nat.ne_of_lt storageInside
  rw [openDestination_transition]
  simp only [lookupStorage_result, bind]
  cases targetFound : state.storage[target]? with
  | none => simpa only [targetFound, ConstructionResult.finalState] using
      (show (state.destinations.extract 0 state.destinations.size, state.storage[sourceStorage]?) =
          (state.destinations, some storage) from by simp [storageFound])
  | some receiver =>
      have targetInside := (Array.getElem?_eq_some_iff.mp targetFound).1
      cases knownCount <;> cases layout <;> cases request : capability.request <;>
          repeat' first
            | rfl
            | simp_all (config := { maxSteps := 500000 }) only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                lookupStorage_result, replaceStorage_result, reserveStorage, emit_result,
                hasPrefix_result, request,
                bind, pure, ConstructionResult.finalState, Array.size_push,
                Array.getElem?_push, Array.set!_eq_setIfInBounds,
                PendingDestination.storage, DestinationBacking.writeStorage, DestinationBacking.receiverStorage,
                Array.getElem?_push_size, targetFound, targetInside,
                Array.extract_push_of_le (Nat.le_refl _), Array.extract_size,
                Array.getElem?_setIfInBounds_ne different.symm,
                Array.getElem?_setIfInBounds_ne storageNotLast.symm,
                storageNotLast, storageInside, ↓reduceIte, storageFound, reduceCtorEq,
                beq_self_eq_true, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
                Bool.not_true, Bool.not_false, Bool.false_eq_true]
            | allocation_split_if
            | split

set_option maxHeartbeats 8000000 in
theorem openDestination_success_storage (state after : ConstructionState)
    (target : StorageId) (capability : Goose.Core.Destination Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) (id cutoff : Nat)
    (targetFresh : cutoff ≤ target) (stagingFresh : cutoff ≤ state.storage.size)
    (executed : openDestination target capability layout knownCount state = .ok id after) :
    ∃ destination, after.destinations[id]? = some destination ∧
      destination.backing.receiverStorage = target ∧ cutoff ≤ destination.storage := by
  rw [openDestination_transition] at executed
  simp only [lookupStorage_result, bind] at executed
  cases targetFound : state.storage[target]? with
  | none => simp only [targetFound] at executed; cases executed
  | some receiver =>
      have targetInside := (Array.getElem?_eq_some_iff.mp targetFound).1
      cases knownCount <;> cases layout <;> cases request : capability.request <;>
        repeat' first
          | contradiction
          | simp_all (config := { maxSteps := 500000 }) only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
              lookupStorage_result, replaceStorage_result, reserveStorage, emit_result,
              hasPrefix_result, request,
              bind, pure, ConstructionResult.ok.injEq, Array.size_push,
              PendingDestination.storage, DestinationBacking.writeStorage, DestinationBacking.receiverStorage,
              Array.getElem?_push_size, Array.getElem?_push, targetFound, targetInside,
              Nat.lt_succ_self, Nat.lt_irrefl, ↓reduceIte, reduceCtorEq, beq_self_eq_true,
              Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
              Bool.not_true, Bool.not_false, Bool.false_eq_true]
          | allocation_split_if_at executed
          | split at executed
          | rcases executed with ⟨rfl, rfl⟩
      all_goals
        first
          | exact ⟨_, rfl, rfl, targetFresh⟩
          | exact ⟨_, rfl, rfl, stagingFresh⟩

theorem newDestination_existing_source (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (state : ExecutionState) (source : StorageId)
    (storage : ReceivingStorage) (present : state.construction.storage[source]? = some storage) :
    AllocationObservation state
      (Goose.Proofs.Exit.stepState (newDestination layout owner ty request origin none knownCount state)) source := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  let prepared : ExecutionState := { state with construction :=
    { state.construction with storage := state.construction.storage.push ⟨ByteArray.empty, 0⟩ } }
  have sourceFound : prepared.construction.storage[source]? = some storage := by
    simpa only [prepared, Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using present
  have query := Goose.Proofs.ConstructionExecutionProtocol.stateQuery_receivingLayout layout ty prepared
  simp only [newDestination, liftConstruction, reserveStorage, ConstructionM.get,
    ConstructionM.set, bind, pure]
  change AllocationObservation state (Goose.Proofs.Exit.stepState
    ((receivingLayout layout ty >>= fun selected => liftConstruction origin
      (openDestination state.construction.storage.size
        ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount)) prepared)) source
  cases result : receivingLayout layout ty prepared with
  | ok selected after =>
      simp only [result, Goose.Proofs.Exit.stepState] at query
      subst after
      have frame := openDestination_existing_source prepared.construction state.construction.storage.size source
        ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount storage sourceFound
        (Nat.ne_of_lt inside)
      cases opened : openDestination state.construction.storage.size
          ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount prepared.construction <;>
        simp only [opened, ConstructionResult.finalState] at frame <;>
        simpa only [bind, result, liftConstruction, opened, Goose.Proofs.Exit.stepState,
          AllocationObservation, prepared, true_and, present, Prod.mk.injEq] using frame
  | stop reason after | escape target carriers after | jump target kind after =>
      simp only [result, Goose.Proofs.Exit.stepState] at query
      subst after
      simp only [bind, result, Goose.Proofs.Exit.stepState, AllocationObservation, prepared,
        Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte, Array.extract_size,
        true_and, present, and_true]

theorem newDestination_objects (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (state : ExecutionState) :
    let after := Goose.Proofs.Exit.stepState (newDestination layout owner ty request origin none knownCount state)
    after.objects = state.objects ∧ after.objectOrdinals = state.objectOrdinals := by
  let prepared : ExecutionState := { state with construction :=
    { state.construction with storage := state.construction.storage.push ⟨ByteArray.empty, 0⟩ } }
  have query := Goose.Proofs.ConstructionExecutionProtocol.stateQuery_receivingLayout layout ty prepared
  simp only [newDestination, liftConstruction, reserveStorage, ConstructionM.get,
    ConstructionM.set, bind, pure]
  let result := ((receivingLayout layout ty >>= fun selected => liftConstruction origin
      (openDestination state.construction.storage.size
        ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount)) prepared)
  change (Goose.Proofs.Exit.stepState result).objects = state.objects ∧
    (Goose.Proofs.Exit.stepState result).objectOrdinals = state.objectOrdinals
  dsimp only [result]
  cases evaluated : receivingLayout layout ty prepared with
  | ok selected after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at query
      subst after
      cases opened : openDestination state.construction.storage.size
          ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount prepared.construction <;>
        simp only [bind, evaluated, liftConstruction, opened, Goose.Proofs.Exit.stepState, prepared,
          and_self]
  | stop reason after | escape target carriers after | jump target kind after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at query
      subst after
      simp only [bind, evaluated, Goose.Proofs.Exit.stepState, prepared, and_self]

theorem newDestination_success_fresh (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (state after : ExecutionState) (id : DestinationId)
    (executed : newDestination layout owner ty request origin none knownCount state = .ok id after) :
    ∃ destination, after.construction.destinations[id]? = some destination ∧
      destination.backing.receiverStorage = state.construction.storage.size ∧
      state.construction.storage.size ≤ destination.storage := by
  let prepared : ExecutionState := { state with construction :=
    { state.construction with storage := state.construction.storage.push ⟨ByteArray.empty, 0⟩ } }
  have query := Goose.Proofs.ConstructionExecutionProtocol.stateQuery_receivingLayout layout ty prepared
  simp only [newDestination, liftConstruction, reserveStorage, ConstructionM.get,
    ConstructionM.set, bind, pure] at executed
  change ((receivingLayout layout ty >>= fun selected => liftConstruction origin
    (openDestination state.construction.storage.size
      ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount)) prepared) =
      .ok id after at executed
  cases result : receivingLayout layout ty prepared with
  | ok selected middle =>
      simp only [result, Goose.Proofs.Exit.stepState] at query
      subst middle
      simp only [bind, result, liftConstruction] at executed
      cases opened : openDestination state.construction.storage.size
          ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount prepared.construction with
      | fault reason final => simp only [opened] at executed; cases executed
      | ok value final =>
          simp only [opened] at executed
          cases executed
          exact openDestination_success_storage prepared.construction final state.construction.storage.size
            ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount id
            state.construction.storage.size (Nat.le_refl _) (by simp [prepared]) opened
  | stop reason middle | escape target carriers middle | jump target kind middle =>
      simp only [bind, result] at executed
      cases executed

theorem newDestination_existing_storage_separate (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (state after : ExecutionState) (id source : StorageId)
    (storage : ReceivingStorage) (present : state.construction.storage[source]? = some storage)
    (executed : newDestination layout owner ty request origin none knownCount state = .ok id after) :
    ∃ destination, after.construction.destinations[id]? = some destination ∧
      source ≠ destination.storage ∧ source ≠ destination.backing.receiverStorage := by
  obtain ⟨destination, found, receiver, fresh⟩ :=
    newDestination_success_fresh layout owner ty request origin knownCount state after id executed
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  exact ⟨destination, found, Nat.ne_of_lt (Nat.lt_of_lt_of_le inside fresh),
    by rw [receiver]; exact Nat.ne_of_lt inside⟩

theorem ValueStorageBacked.newDestination_frame (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (state : ExecutionState) (value : Value)
    (valid : ValueStorageBacked layout state value) :
    ValueStorageBacked layout
      (Goose.Proofs.Exit.stepState (newDestination layout owner ty request origin none knownCount state)) value := by
  induction valid with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | array values children ih => exact .array values ih
  | record id values children ih => exact .record id values ih
  | stored stored backing =>
      have present : ∃ storage, state.construction.storage[stored.storage]? = some storage := by
        cases backing <;> exact ⟨_, by assumption⟩
      obtain ⟨storage, found⟩ := present
      exact .stored stored (backing.allocation_frame layout state _ stored
        (newDestination_existing_source layout owner ty request origin knownCount state stored.storage storage found))

theorem RootedBackingState.newDestination_frame (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (state : ExecutionState) (retainedRoot : Goose.Core.RootInst → Prop)
    (valid : RootedBackingState layout state retainedRoot) :
    RootedBackingState layout
      (Goose.Proofs.Exit.stepState (newDestination layout owner ty request origin none knownCount state)) retainedRoot := by
  have objects := newDestination_objects layout owner ty request origin knownCount state
  constructor
  · intro root retained value present
    rw [objects.1] at present
    exact (valid.values root retained value present).newDestination_frame layout owner ty request origin knownCount state value
  · intro root retained stored present
    rw [objects.1] at present
    rw [objects.2]
    exact valid.identities root retained stored present

#print axioms openDestination_existing_source
#print axioms newDestination_existing_source
#print axioms StoredValueBacking.allocation_frame
#print axioms newDestination_objects
#print axioms openDestination_success_storage
#print axioms newDestination_success_fresh
#print axioms newDestination_existing_storage_separate
#print axioms ValueStorageBacked.newDestination_frame
#print axioms RootedBackingState.newDestination_frame

end Goose.Proofs.ConstructionRepresentation
