import Goose.Proofs.ConstructionFreshByteWriteEvents
import Goose.Proofs.ConstructionByteAllocationStopped
import Lean.Elab.Tactic.Split

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

local syntax "byte_events_split " ident : tactic
elab_rules : tactic
  | `(tactic| byte_events_split $name:ident) => do
      let hypothesis ← Lean.Elab.Tactic.getFVarId name
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.SplitIf.splitIfAt? goal (← Lean.Meta.inferType (.fvar hypothesis)) none
          | Lean.throwError "no allocation condition"
        return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 1200000 in
private theorem openPacked_success_events (state after : ConstructionState) (target count id : Nat)
    (capability : Goose.Core.Destination Ty) (request : capability.request = .value)
    (executed : openDestination target capability .packed (some count) state = .ok id after) :
    after.events = state.events ++ [.begin id] := by
  rw [openDestination_transition] at executed
  simp only [lookupStorage_result, bind] at executed
  cases targetFound : state.storage[target]? with
  | none => simp only [targetFound] at executed; cases executed
  | some receiver =>
    have targetInside := (Array.getElem?_eq_some_iff.mp targetFound).1
    repeat' first
      | contradiction
      | simp_all only [ConstructionM.get, ConstructionM.set, ConstructionM.fail, available_result,
          replaceStorage_result, emit_result, hasPrefix_result, pure,
          ConstructionResult.ok.injEq, PendingDestination.storage,
          DestinationBacking.writeStorage, DestinationBacking.receiverStorage,
          Nat.lt_irrefl, ↓reduceIte, reduceCtorEq,
          beq_self_eq_true, Bool.and_true, Bool.false_eq_true]
      | byte_events_split executed
      | split at executed
      | rcases executed with ⟨rfl, rfl⟩
    all_goals rfl

theorem newDestination_byteOwner_success_events (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (origin : Goose.Core.OriginId) (count : Nat) (before after : ExecutionState) (id : Nat)
    (executed : newDestination layout owner (.varr (.int .u8)) .value origin none (some count) before = .ok id after) :
    after.construction.events = before.construction.events ++ [.begin id] := by
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
    simp only [opened] at executed
    cases executed
    exact openPacked_success_events prepared.construction final before.construction.storage.size count id _ rfl opened

theorem newDestination_byteOwner_stopped_events (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (origin : Goose.Core.OriginId) (count : Nat) (before after : ExecutionState) (stop : Goose.Core.Stop)
    (executed : newDestination layout owner (.varr (.int .u8)) .value origin none (some count) before = .stop stop after) :
    after.construction.events = before.construction.events := by
  rw [newDestination_byteOwner_stopped_state layout owner origin count before after stop executed]

#print axioms newDestination_byteOwner_success_events
#print axioms newDestination_byteOwner_stopped_events

end Goose.Proofs.ConstructionAcceptedExecution
