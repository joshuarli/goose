import Goose.Proofs.ConstructionAcceptedAllocation
import Goose.Proofs.ConstructionRootedBackingAllocation
import Goose.Proofs.ExitExecutionReceiverReadiness
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

local syntax "open_geometry_split " ident : tactic
elab_rules : tactic
  | `(tactic| open_geometry_split $name:ident) => do
      let hypothesis ← Lean.Elab.Tactic.getFVarId name
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.SplitIf.splitIfAt? goal (← Lean.Meta.inferType (.fvar hypothesis)) none
          | Lean.throwError "no open destination condition"
        return [yes.mvarId, no.mvarId]

def destinationPayloadStart (destination : PendingDestination) : Nat :=
  destination.capability.start +
    if destination.layout == .packed && destination.capability.request == .value then 4 else 0

structure OpenDestinationBacking (layout : LayoutEnv) (state : ExecutionState) (id : Nat) (ty : Ty) (count : Nat) where
  destination : PendingDestination
  storage : ReceivingStorage
  present : state.construction.destinations[id]? = some destination
  bytes : state.construction.storage[destination.storage]? = some storage
  logicalType : destination.capability.logicalType = ty
  opened : destination.progress = .open count
  element : Ty
  elementType : Goose.Construct.elementType ty = some element
  fuel : Nat
  scan : elementsEnd fuel layout element count storage.bytes (destinationPayloadStart destination) =
    .ok destination.writeEnd
  bounded : destination.writeEnd ≤ storage.bytes.size
  rollback : destination.rollbackEnd ≤ storage.bytes.size

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem openDestination_initial_geometry (state after : ConstructionState) (target : Nat)
    (capability : Goose.Core.Destination Ty) (selected : ReceivingLayout) (knownCount : Option Nat)
    (id : Nat) (executed : openDestination target capability selected knownCount state = .ok id after) :
    ∃ destination storage, after.destinations[id]? = some destination ∧
      after.storage[destination.storage]? = some storage ∧
      destination.capability.logicalType = capability.logicalType ∧ destination.progress = .open 0 ∧
      destinationPayloadStart destination = destination.writeEnd ∧
      destination.writeEnd ≤ storage.bytes.size ∧ destination.rollbackEnd ≤ storage.bytes.size := by
  rw [openDestination_transition] at executed
  simp only [lookupStorage_result, bind] at executed
  cases targetFound : state.storage[target]? with
  | none => simp only [targetFound] at executed; cases executed
  | some receiver =>
    have targetInside := (Array.getElem?_eq_some_iff.mp targetFound).1
    cases knownCount <;> cases selected <;> cases request : capability.request <;>
      repeat' first
        | contradiction
        | simp_all only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
            replaceStorage_result, reserveStorage, emit_result, hasPrefix_result, bind, pure,
            ConstructionResult.ok.injEq, Array.size_push, PendingDestination.storage,
            DestinationBacking.writeStorage, DestinationBacking.receiverStorage,
            Array.getElem?_push, Array.getElem?_setIfInBounds, Nat.lt_irrefl, ↓reduceIte,
            reduceCtorEq, beq_self_eq_true, Bool.true_and, Bool.and_true, Bool.and_false,
            Bool.false_eq_true]
        | open_geometry_split executed
        | split at executed
        | rcases executed with ⟨rfl, rfl⟩
    all_goals simp_all [destinationPayloadStart, PendingDestination.storage,
      DestinationBacking.writeStorage, Array.getElem?_push, Array.getElem?_setIfInBounds, ByteArray.size_append]
    all_goals exact Nat.le_refl 4

theorem openDestination_initial_backing (layout : LayoutEnv) (state after : ConstructionState) (target : Nat)
    (capability : Goose.Core.Destination Ty) (selected : ReceivingLayout) (knownCount : Option Nat)
    (id : Nat) (executed : openDestination target capability selected knownCount state = .ok id after)
    (execution : ExecutionState) (construction : execution.construction = after)
    (element : Ty) (elementType : Goose.Construct.elementType capability.logicalType = some element) :
    Nonempty (OpenDestinationBacking layout execution id capability.logicalType 0) := by
  obtain ⟨destination, storage, present, stored, logicalType, opened, start, bounded, rollback⟩ :=
    openDestination_initial_geometry state after target capability selected knownCount id executed
  refine ⟨⟨destination, storage, ?_, ?_, logicalType, opened, element, elementType, 1, ?_, bounded, rollback⟩⟩
  · rw [construction]
    exact present
  · rw [construction]
    exact stored
  · simp only [elementsEnd, start]

theorem newDestination_initial_backing (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId) (knownCount : Option Nat)
    (state after : ExecutionState) (id : Nat) (element : Ty)
    (elementType : Goose.Construct.elementType ty = some element)
    (executed : newDestination layout owner ty request origin none knownCount state = .ok id after) :
    Nonempty (OpenDestinationBacking layout after id ty 0) := by
  let prepared : ExecutionState := { state with construction :=
    { state.construction with storage := state.construction.storage.push ⟨ByteArray.empty, 0⟩ } }
  have query := Goose.Proofs.ConstructionExecutionProtocol.stateQuery_receivingLayout layout ty prepared
  simp only [newDestination, liftConstruction, reserveStorage, ConstructionM.get,
    ConstructionM.set, bind, pure] at executed
  change ((receivingLayout layout ty >>= fun selected => liftConstruction origin
    (openDestination state.construction.storage.size
      ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount)) prepared) = .ok id after at executed
  cases received : receivingLayout layout ty prepared with
  | ok selected middle =>
    simp only [received, Goose.Proofs.Exit.stepState] at query
    subst middle
    simp only [bind, received, liftConstruction] at executed
    cases opened : openDestination state.construction.storage.size
        ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount prepared.construction with
    | fault reason final => simp only [opened] at executed; cases executed
    | ok value final =>
      simp only [opened] at executed
      cases executed
      exact openDestination_initial_backing layout prepared.construction final state.construction.storage.size
        _ selected knownCount id opened _ rfl element elementType
  | stop reason middle | escape target carriers middle | jump target kind middle =>
    simp only [bind, received] at executed
    cases executed

theorem newDestination_open_ready (config : EvalConfig) (initialized : Nat) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId) (knownCount : Option Nat)
    (before after : ExecutionState) (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient)
    (types : RootTypes) (liveRoots : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (id : Nat) (element : Ty)
    (world : AcceptedWorld config initialized before ambient types liveRoots regions pending)
    (elementType : Goose.Construct.elementType ty = some element)
    (executed : newDestination config.layout owner ty request origin none knownCount before = .ok id after) :
    Nonempty (OpenDestinationBacking config.layout after id ty 0) ∧
      Nonempty (Goose.Proofs.ExitExecution.ReceivingCarrierLandingReady after id id) :=
  ⟨newDestination_initial_backing config.layout owner ty request origin knownCount before after id element elementType executed,
    Goose.Proofs.ExitExecution.newDestination_receiving_ready config.layout owner ty request origin none knownCount
      before after id world.ownership.source.structural.2.1 executed⟩

#print axioms openDestination_initial_geometry
#print axioms newDestination_initial_backing
#print axioms newDestination_open_ready

end Goose.Proofs.ConstructionAcceptedExecution
