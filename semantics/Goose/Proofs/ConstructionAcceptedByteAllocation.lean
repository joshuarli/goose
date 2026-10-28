import Goose.Proofs.ConstructionAcceptedByteBacking
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

local syntax "byte_allocation_split " ident : tactic
elab_rules : tactic
  | `(tactic| byte_allocation_split $name:ident) => do
      let hypothesis ← Lean.Elab.Tactic.getFVarId name
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.SplitIf.splitIfAt? goal (← Lean.Meta.inferType (.fvar hypothesis)) none
          | Lean.throwError "no allocation condition"
        return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 1200000 in
theorem openDestination_packed_value_with_physical (state after : ConstructionState) (target : Nat)
    (capability : Goose.Core.Destination Ty) (knownCount : Option Nat) (id : Nat)
    (request : capability.request = .value)
    (executed : openDestination target capability .packed knownCount state = .ok id after) :
    ∃ destination, after.destinations[id]? = some destination ∧
      destination.layout = .packed ∧ destination.capability.request = .value ∧
      destination.backing = .direct target ∧ destination.use = .receiver ∧ destination.adaptation = none ∧ destination.capability.layout = capability.layout := by
  rw [openDestination_transition] at executed
  simp only [lookupStorage_result, bind] at executed
  cases targetFound : state.storage[target]? with
  | none => simp only [targetFound] at executed; cases executed
  | some receiver =>
    have targetInside := (Array.getElem?_eq_some_iff.mp targetFound).1
    cases knownCount <;>
      repeat' first
        | contradiction
        | simp_all only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
            replaceStorage_result, emit_result, hasPrefix_result, pure,
            ConstructionResult.ok.injEq, PendingDestination.storage,
            DestinationBacking.writeStorage, DestinationBacking.receiverStorage,
            Array.getElem?_push, Nat.lt_irrefl, ↓reduceIte,
            reduceCtorEq, beq_self_eq_true, Bool.and_true,
            Bool.false_eq_true]
        | byte_allocation_split executed
        | split at executed
        | rcases executed with ⟨rfl, rfl⟩
    all_goals exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩



set_option maxHeartbeats 1200000 in
theorem openDestination_packed_value_with_adaptation (state after : ConstructionState) (target : Nat)
    (capability : Goose.Core.Destination Ty) (knownCount : Option Nat) (id : Nat)
    (request : capability.request = .value)
    (executed : openDestination target capability .packed knownCount state = .ok id after) :
    ∃ destination, after.destinations[id]? = some destination ∧
      destination.layout = .packed ∧ destination.capability.request = .value ∧
      destination.backing = .direct target ∧ destination.use = .receiver ∧ destination.adaptation = none := by
  obtain ⟨destination, found, packed, request, backing, receiver, adaptation, physical⟩ :=
    openDestination_packed_value_with_physical state after target capability knownCount id request executed
  exact ⟨destination, found, packed, request, backing, receiver, adaptation⟩

theorem openDestination_packed_value (state after : ConstructionState) (target : Nat)
    (capability : Goose.Core.Destination Ty) (knownCount : Option Nat) (id : Nat)
    (request : capability.request = .value)
    (executed : openDestination target capability .packed knownCount state = .ok id after) :
    ∃ destination, after.destinations[id]? = some destination ∧
      destination.layout = .packed ∧ destination.capability.request = .value ∧
      destination.backing = .direct target ∧ destination.use = .receiver := by
  obtain ⟨destination, found, packed, request, backing, receiver, adaptation⟩ :=
    openDestination_packed_value_with_adaptation state after target capability knownCount id request executed
  exact ⟨destination, found, packed, request, backing, receiver⟩

theorem openDestination_packed_count_bound (state after : ConstructionState) (target : Nat)
    (capability : Goose.Core.Destination Ty) (count id : Nat)
    (executed : openDestination target capability .packed (some count) state = .ok id after) :
    count < 2 ^ 32 := by
  by_cases fits : count < 2 ^ 32
  · exact fits
  · rw [openDestination_transition] at executed
    simp only [lookupStorage_result, bind] at executed
    cases found : state.storage[target]? with
    | none => simp only [found] at executed; cases executed
    | some storage =>
      simp only [found, ConstructionM.get, available_result, fits, decide_false,
        Bool.not_false, ↓reduceIte, ConstructionM.fail] at executed
      split at executed <;> cases executed

theorem newDestination_byteOwner_packed_value_with_physical (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (origin : Goose.Core.OriginId) (knownCount : Option Nat) (before after : ExecutionState) (id : Nat)
    (executed : newDestination layout owner (.varr (.int .u8)) .value origin none knownCount before = .ok id after) :
    ∃ destination, after.construction.destinations[id]? = some destination ∧
      destination.layout = .packed ∧ destination.capability.request = .value ∧
      destination.backing = .direct before.construction.storage.size ∧ destination.use = .receiver ∧ destination.adaptation = none ∧ destination.capability.layout = .varr (.int .u8) := by
  let prepared : ExecutionState := { before with construction :=
    { before.construction with storage := before.construction.storage.push ⟨ByteArray.empty, 0⟩ } }
  simp only [newDestination, liftConstruction, reserveStorage, ConstructionM.get,
    ConstructionM.set, bind, pure] at executed
  change ((receivingLayout layout (.varr (.int .u8)) >>= fun selected => liftConstruction origin
    (openDestination before.construction.storage.size
      ⟨0, ⟨.local owner 0 0, []⟩, .varr (.int .u8), .varr (.int .u8), .value, 0, owner⟩ selected knownCount))
      prepared) = .ok id after at executed
  simp only [receivingLayout, pure, bind, liftConstruction] at executed
  cases opened : openDestination before.construction.storage.size
      ⟨0, ⟨.local owner 0 0, []⟩, .varr (.int .u8), .varr (.int .u8), .value, 0, owner⟩
      .packed knownCount prepared.construction with
  | fault reason final => simp only [opened] at executed; cases executed
  | ok value final =>
    simp only [opened] at executed
    cases executed
    exact openDestination_packed_value_with_physical prepared.construction final before.construction.storage.size _ knownCount id rfl opened



theorem newDestination_byteOwner_packed_value_with_adaptation (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (origin : Goose.Core.OriginId) (knownCount : Option Nat) (before after : ExecutionState) (id : Nat)
    (executed : newDestination layout owner (.varr (.int .u8)) .value origin none knownCount before = .ok id after) :
    ∃ destination, after.construction.destinations[id]? = some destination ∧
      destination.layout = .packed ∧ destination.capability.request = .value ∧
      destination.backing = .direct before.construction.storage.size ∧ destination.use = .receiver ∧ destination.adaptation = none := by
  obtain ⟨destination, found, packed, request, backing, receiver, adaptation, physical⟩ :=
    newDestination_byteOwner_packed_value_with_physical layout owner origin knownCount before after id executed
  exact ⟨destination, found, packed, request, backing, receiver, adaptation⟩

theorem newDestination_byteOwner_packed_value (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (origin : Goose.Core.OriginId) (knownCount : Option Nat) (before after : ExecutionState) (id : Nat)
    (executed : newDestination layout owner (.varr (.int .u8)) .value origin none knownCount before = .ok id after) :
    ∃ destination, after.construction.destinations[id]? = some destination ∧
      destination.layout = .packed ∧ destination.capability.request = .value ∧
      destination.backing = .direct before.construction.storage.size ∧ destination.use = .receiver := by
  obtain ⟨destination, found, packed, request, backing, receiver, adaptation⟩ :=
    newDestination_byteOwner_packed_value_with_adaptation layout owner origin knownCount before after id executed
  exact ⟨destination, found, packed, request, backing, receiver⟩

theorem newDestination_byteOwner_count_bound (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (origin : Goose.Core.OriginId) (count : Nat) (before after : ExecutionState) (id : Nat)
    (executed : newDestination layout owner (.varr (.int .u8)) .value origin none (some count) before = .ok id after) :
    count < 2 ^ 32 := by
  let prepared : ExecutionState := { before with construction :=
    { before.construction with storage := before.construction.storage.push ⟨ByteArray.empty, 0⟩ } }
  simp only [newDestination, liftConstruction, reserveStorage, ConstructionM.get,
    ConstructionM.set, bind, pure] at executed
  change ((receivingLayout layout (.varr (.int .u8)) >>= fun selected => liftConstruction origin
    (openDestination before.construction.storage.size
      ⟨0, ⟨.local owner 0 0, []⟩, .varr (.int .u8), .varr (.int .u8), .value, 0, owner⟩ selected (some count)))
      prepared) = .ok id after at executed
  simp only [receivingLayout, pure, bind, liftConstruction] at executed
  cases opened : openDestination before.construction.storage.size
      ⟨0, ⟨.local owner 0 0, []⟩, .varr (.int .u8), .varr (.int .u8), .value, 0, owner⟩
      .packed (some count) prepared.construction with
  | fault reason final => simp only [opened] at executed; cases executed
  | ok value final =>
    exact openDestination_packed_count_bound prepared.construction final before.construction.storage.size _ count value opened

theorem allocated_byteOwner_backing (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before allocated built : ExecutionState) (id : Nat)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none (some bytes.length) before =
      .ok id allocated)
    (constructed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) allocated =
      .ok () built) :
    ∃ value, storedDestination id built = .ok value built ∧
      Goose.Proofs.ConstructionRepresentation.StoredValueBacking config.layout built value := by
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout environment.act (.varr (.int .u8)) .value
    origin (some bytes.length) before allocated id (.int .u8) rfl created
  obtain ⟨destination, present, packed, request, backing, use⟩ := newDestination_byteOwner_packed_value config.layout
    environment.act origin (some bytes.length) before allocated id created
  have same : destination = ready.destination := Option.some.inj (present.symm.trans ready.present)
  subst destination
  have allocatedWorld := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) initialized before allocated id ambient types live regions pending world created
  have current := newDestination_current_self config initialized environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id ambient types live regions pending world created
  have fits := newDestination_byteOwner_count_bound config.layout environment.act origin bytes.length before allocated id created
  exact buildExpr_byteOwner_backing fuel config environment bytes origin id 0 allocated built ready packed request
    (by simpa using fits) allocatedWorld.ownership.source.structural.1.1.1 current constructed

#print axioms openDestination_packed_value
#print axioms openDestination_packed_value_with_physical
#print axioms openDestination_packed_value_with_adaptation
#print axioms openDestination_packed_count_bound
#print axioms newDestination_byteOwner_packed_value
#print axioms newDestination_byteOwner_packed_value_with_physical
#print axioms newDestination_byteOwner_packed_value_with_adaptation
#print axioms newDestination_byteOwner_count_bound
#print axioms allocated_byteOwner_backing

end Goose.Proofs.ConstructionAcceptedExecution
