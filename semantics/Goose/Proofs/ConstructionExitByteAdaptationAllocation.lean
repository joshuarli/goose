import Goose.Proofs.ConstructionAcceptedByteAllocation
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

local syntax "exit_allocation_split " ident : tactic
elab_rules : tactic
  | `(tactic| exit_allocation_split $name:ident) => do
      let hypothesis ← Lean.Elab.Tactic.getFVarId name
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.SplitIf.splitIfAt? goal (← Lean.Meta.inferType (.fvar hypothesis)) none
          | Lean.throwError "no allocation condition"
        return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 1200000 in
theorem exit_openDestination_packed_adaptation (state after : ConstructionState) (target : Nat)
    (capability : Goose.Core.Destination Ty) (knownCount : Option Nat) (id : Nat)
    (request : capability.request = .value)
    (executed : openDestination target capability .packed knownCount state = .ok id after) :
    ∃ destination, after.destinations[id]? = some destination ∧
      destination.layout = .packed ∧ destination.capability.request = .value ∧
      destination.backing = .direct target ∧ destination.use = .receiver ∧ destination.adaptation = none := by
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
        | exit_allocation_split executed
        | split at executed
        | rcases executed with ⟨rfl, rfl⟩
    all_goals exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem exit_newDestination_byte_adaptation (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (origin : Goose.Core.OriginId) (knownCount : Option Nat) (before after : ExecutionState) (id : Nat)
    (executed : newDestination layout owner (.varr (.int .u8)) .value origin none knownCount before = .ok id after) :
    ∃ destination, after.construction.destinations[id]? = some destination ∧
      destination.layout = .packed ∧ destination.capability.request = .value ∧
      destination.backing = .direct before.construction.storage.size ∧ destination.use = .receiver ∧ destination.adaptation = none := by
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
    exact exit_openDestination_packed_adaptation prepared.construction final before.construction.storage.size _ knownCount id rfl opened


#print axioms exit_newDestination_byte_adaptation

end Goose.Proofs.ConstructionAcceptedExecution
