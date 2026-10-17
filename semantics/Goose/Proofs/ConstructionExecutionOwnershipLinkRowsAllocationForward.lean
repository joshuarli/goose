import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsAllocation
import Goose.Proofs.ConstructionExecutionOwnershipLinkExtensions

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

local syntax "allocation_forward_split_if" : tactic
elab_rules : tactic
  | `(tactic| allocation_forward_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no ownership allocation condition to split"
      return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 2000000 in
theorem openDestinationDirect_forwardLinks (storageId : StorageId)
    (capability : Core.Destination Construct.Ty) (layout : ReceivingLayout) (knownCount : Option Nat)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) (links : DestinationForwardLinks state) :
    DestinationForwardLinks (openDestinationDirect storageId capability layout knownCount state).finalState := by
  rw [openDestinationDirect_transition]
  simp only [lookupStorage_result, bind]
  cases stored : state.storage[storageId]? with
  | none => exact links
  | some receiving =>
      simp only [stored]
      have storageInside := (Array.getElem?_eq_some_iff.mp stored).choose
      have allocated : ∀ (start writeEnd rollbackEnd : Nat) (storage : Array ReceivingStorage),
          storage.size = state.storage.size →
          DestinationForwardLinks { state with
            storage := storage
            destinations := state.destinations.push
              ⟨{ capability with id := state.destinations.size, start := start }, .direct storageId,
                layout, .receiver, .open 0, writeEnd, rollbackEnd, knownCount, none⟩
            events := state.events ++ [.begin state.destinations.size] } := by
        intro start writeEnd rollbackEnd storage size
        exact destinationForwardLinks_push_open state _ 0 rfl links
      cases layout <;> cases knownCount
      all_goals repeat' first
        | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
            lookupStorage_result, stored, DestinationBacking.writeStorage,
            replaceStorage_result, storageInside, emit_result, Nat.lt_irrefl,
            ↓reduceIte, bind, pure, ConstructionResult.finalState]
        | allocation_forward_split_if
        | exact links
        | exact allocated _ _ _ _ (by simp)

set_option maxHeartbeats 2000000 in
theorem openDestination_forwardLinks (storageId : StorageId)
    (capability : Core.Destination Construct.Ty) (layout : ReceivingLayout) (knownCount : Option Nat)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) (links : DestinationForwardLinks state) :
    DestinationForwardLinks (openDestination storageId capability layout knownCount state).finalState := by
  cases layout with
  | packed =>
      simpa only [openDestination_transition, openDestinationDirect_transition] using
        openDestinationDirect_forwardLinks storageId capability .packed knownCount state valid links
  | elements =>
      simpa only [openDestination_transition, openDestinationDirect_transition] using
        openDestinationDirect_forwardLinks storageId capability .elements knownCount state valid links
  | fixed expected =>
      simpa only [openDestination_transition, openDestinationDirect_transition] using
        openDestinationDirect_forwardLinks storageId capability (.fixed expected) knownCount state valid links
  | limited capacity slotBytes =>
      cases knownCount with
      | some count =>
          simpa only [openDestination_transition, openDestinationDirect_transition] using
            openDestinationDirect_forwardLinks storageId capability
              (.limited capacity slotBytes) (some count) state valid links
      | none =>
          rw [openDestination_transition]
          simp only [lookupStorage_result, bind]
          cases stored : state.storage[storageId]? with
          | none => exact links
          | some receiving =>
              simp only [stored]
              have storageInside := (Array.getElem?_eq_some_iff.mp stored).choose
              let reserved : ConstructionState := { state with storage := state.storage.push ⟨ByteArray.empty, 0⟩ }
              have reservedValid : DestinationLifecycleInvariant reserved :=
                reserveStorage_destination_lifecycle_invariant ByteArray.empty 0 state valid
              have reservedFrame : DestinationForwardLinks reserved := links
              have allocated : ∀ (start writeEnd rollbackEnd : Nat) (storage : Array ReceivingStorage),
                  storage.size = reserved.storage.size →
                  DestinationForwardLinks { reserved with
                    storage := storage
                    destinations := reserved.destinations.push
                      ⟨{ capability with id := state.destinations.size, start := start },
                        .staged storageId state.storage.size, .limited capacity slotBytes, .receiver,
                        .open 0, writeEnd, rollbackEnd, none, none⟩
                    events := state.events ++ [.begin state.destinations.size, .stage state.destinations.size] } := by
                intro start writeEnd rollbackEnd storage size
                exact destinationForwardLinks_push_open state _ 0 rfl links
              repeat' first
                | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                    reserveStorage, lookupStorage_result, DestinationBacking.writeStorage,
                    Array.getElem?_push_size, Nat.lt_irrefl,
                    replaceStorage_result, Array.size_push, Nat.lt_succ_self, emit_result,
                    ↓reduceIte, bind, pure, ConstructionResult.finalState, List.append_assoc]
                | allocation_forward_split_if
                | exact links
                | exact reservedFrame
                | exact allocated _ _ _ _ (by simp [reserved])

end Goose.Proofs.ConstructionExecutionOwnership
