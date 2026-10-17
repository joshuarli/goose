import Goose.Proofs.ConstructionExecutionOwnershipSourceMutations
import Goose.Proofs.ConstructionExecutionProtocolPrimitives
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

local syntax "source_allocation_split_if" : tactic
elab_rules : tactic
  | `(tactic| source_allocation_split_if) =>
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.splitIfTarget? goal
          | Lean.throwError "no allocation condition to split"
        return [yes.mvarId, no.mvarId]

private theorem source_allocate (state : ConstructionState) (parentId : DestinationId)
    (parent child : PendingDestination) (phase : DestinationProgress)
    (present : state.destinations[parentId]? = some parent) :
    OwnershipSourceExtension state { state with
      destinations := (state.destinations.push child).set! parentId { parent with progress := phase } } := by
  let pushed := { state with destinations := state.destinations.push child }
  have parentPresent : pushed.destinations[parentId]? = some parent := by
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    simpa [pushed, Array.getElem?_push, Nat.ne_of_lt inside] using present
  exact ownershipSourceExtension_trans state pushed _
    (ownershipSourceExtension_push state child)
    (ownershipSourceExtension_replace pushed parentId parent _ parentPresent rfl
      (by cases parentUse : parent.use <;> simp [OwnershipLinkBacking, parentUse]))

theorem openChild_ownership_source (parentId : DestinationId) (logicalType : Construct.Ty)
    (layout : ReceivingLayout) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipSourceExtension state (openChild parentId logicalType layout state).finalState := by
  simp only [openChild, writableDestination_result, bind]
  cases present : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [present]
      cases allowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have insideAfter := Nat.lt_succ_of_lt inside
          have storageInside := (valid.2.2.1 parentId parent present).1
          cases progress : parent.progress <;> try simp only [progress] <;> try exact .refl state
          case «open» count =>
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => exact .refl state
            | some receiving =>
                simp only [stored]
                repeat' first
                  | exact .refl state
                  | solve
                    | exact source_allocate state parentId parent _ _ present
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      replaceDestination_result, replaceStorage_result, emit_result,
                      Array.size_push, insideAfter, storageInside, ↓reduceIte,
                      bind, pure, ConstructionResult.finalState]
                  | source_allocation_split_if
                  | split

set_option maxHeartbeats 800000 in
theorem openElementExtension_ownership_source (parentId : DestinationId) (logicalType : Construct.Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) (receiverLoc : Core.Loc) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipSourceExtension state (openElementExtension parentId logicalType layout knownCount receiverLoc state).finalState := by
  simp only [openElementExtension, writableDestination_result, bind]
  cases present : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [present]
      cases allowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have insideAfter := Nat.lt_succ_of_lt inside
          have storageInside := (valid.2.2.1 parentId parent present).1
          cases progress : parent.progress <;> try simp only [progress] <;> try exact .refl state
          case built count =>
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none =>
                have outside := Array.getElem?_eq_none_iff.mp stored
                exact False.elim (Nat.not_le_of_lt storageInside outside)
            | some receiving =>
                try simp only [stored]
                cases parentLayout : parent.layout <;> cases parentBacking : parent.backing
                all_goals repeat' first
                  | exact .refl state
                  | solve
                    | simp only [← parentLayout, ← parentBacking]
                      exact source_allocate state parentId parent _ _ present
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      replaceDestination_result, replaceStorage_result, emit_result,
                      Array.size_push, insideAfter, storageInside, stored, parentLayout, parentBacking, ↓reduceIte,
                      bind, pure, ConstructionResult.finalState]
                  | source_allocation_split_if
                  | split


theorem openExitReplacement_ownership_source (parentId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipSourceExtension state (openExitReplacement parentId state).finalState := by
  simp only [openExitReplacement, writableDestination_result, bind]
  cases present : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [present]
      cases allowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have insideAfter := Nat.lt_succ_of_lt inside
          have storageInside := (valid.2.2.1 parentId parent present).1
          cases progress : parent.progress <;> try simp only [progress] <;> try exact .refl state
          all_goals
            try simp only [pure, bind]
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => exact .refl state
            | some receiving =>
                simp only [stored]
                repeat' first
                  | exact .refl state
                  | solve
                      | exact source_allocate state parentId parent _ _ present
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      replaceDestination_result, replaceStorage_result, emit_result,
                      Array.size_push, insideAfter, storageInside, ↓reduceIte,
                      bind, pure, ConstructionResult.finalState]
                  | source_allocation_split_if
                  | split


set_option maxHeartbeats 2000000 in
theorem openExtension_ownership_source (parentId : DestinationId)
    (request : ConstructionRequest) (knownCount : Option Nat)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipSourceExtension state (openExtension parentId request knownCount state).finalState := by
  simp only [openExtension, writableDestination_result, bind]
  cases present : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [present]
      cases allowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have insideAfter := Nat.lt_succ_of_lt inside
          have storageInside := (valid.2.2.1 parentId parent present).1
          let reserved : ConstructionState := { state with storage := state.storage.push ⟨ByteArray.empty, 0⟩ }
          have reservedFrame : OwnershipSourceExtension state reserved := .refl state
          cases progress : parent.progress <;> try simp only [progress] <;> try exact .refl state
          case built count =>
            simp only [pure, lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => exact .refl state
            | some receiving =>
                try simp only [stored]
                cases parentLayout : parent.layout <;> cases parentBacking : parent.backing <;> cases knownCount
                all_goals repeat' first
                  | exact .refl state
                  | exact reservedFrame
                  | solve
                    | simp only [← parentLayout, ← parentBacking]
                      exact source_allocate state parentId parent _ _ present
                  | solve
                    | simp only [← parentLayout, ← parentBacking]
                      exact source_allocate reserved parentId parent _ _ present
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      reserveStorage, replaceDestination_result, emit_result,
                      Array.size_push, insideAfter, storageInside, stored, parentLayout, parentBacking,
                      ↓reduceIte, bind, pure, ConstructionResult.finalState, List.append_assoc]
                  | source_allocation_split_if
                  | split

set_option maxHeartbeats 2000000 in
theorem openDestinationDirect_ownership_source (storageId : StorageId)
    (capability : Core.Destination Construct.Ty) (layout : ReceivingLayout) (knownCount : Option Nat)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipSourceExtension state (openDestinationDirect storageId capability layout knownCount state).finalState := by
  rw [openDestinationDirect_transition]
  simp only [lookupStorage_result, bind]
  cases stored : state.storage[storageId]? with
  | none => exact .refl state
  | some receiving =>
      simp only [stored]
      have storageInside := (Array.getElem?_eq_some_iff.mp stored).choose
      have allocated : ∀ (start writeEnd rollbackEnd : Nat) (storage : Array ReceivingStorage),
          storage.size = state.storage.size →
          OwnershipSourceExtension state { state with
            storage := storage
            destinations := state.destinations.push
              ⟨{ capability with id := state.destinations.size, start := start }, .direct storageId,
                layout, .receiver, .open 0, writeEnd, rollbackEnd, knownCount, none⟩
            events := state.events ++ [.begin state.destinations.size] } := by
        intro start writeEnd rollbackEnd storage size
        exact ownershipSourceExtension_push state _
      cases layout <;> cases knownCount
      all_goals repeat' first
        | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
            lookupStorage_result, stored, DestinationBacking.writeStorage,
            replaceStorage_result, storageInside, emit_result, Nat.lt_irrefl,
            ↓reduceIte, bind, pure, ConstructionResult.finalState]
        | source_allocation_split_if
        | exact .refl state
        | exact allocated _ _ _ _ (by simp)

set_option maxHeartbeats 2000000 in
theorem openDestination_ownership_source (storageId : StorageId)
    (capability : Core.Destination Construct.Ty) (layout : ReceivingLayout) (knownCount : Option Nat)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipSourceExtension state (openDestination storageId capability layout knownCount state).finalState := by
  cases layout with
  | packed =>
      simpa only [openDestination_transition, openDestinationDirect_transition] using
        openDestinationDirect_ownership_source storageId capability .packed knownCount state valid
  | elements =>
      simpa only [openDestination_transition, openDestinationDirect_transition] using
        openDestinationDirect_ownership_source storageId capability .elements knownCount state valid
  | fixed expected =>
      simpa only [openDestination_transition, openDestinationDirect_transition] using
        openDestinationDirect_ownership_source storageId capability (.fixed expected) knownCount state valid
  | limited capacity slotBytes =>
      cases knownCount with
      | some count =>
          simpa only [openDestination_transition, openDestinationDirect_transition] using
            openDestinationDirect_ownership_source storageId capability
              (.limited capacity slotBytes) (some count) state valid
      | none =>
          rw [openDestination_transition]
          simp only [lookupStorage_result, bind]
          cases stored : state.storage[storageId]? with
          | none => exact .refl state
          | some receiving =>
              simp only [stored]
              have storageInside := (Array.getElem?_eq_some_iff.mp stored).choose
              let reserved : ConstructionState := { state with storage := state.storage.push ⟨ByteArray.empty, 0⟩ }
              have reservedFrame : OwnershipSourceExtension state reserved := .refl state
              have allocated : ∀ (start writeEnd rollbackEnd : Nat) (storage : Array ReceivingStorage),
                  storage.size = reserved.storage.size →
                  OwnershipSourceExtension state { reserved with
                    storage := storage
                    destinations := reserved.destinations.push
                      ⟨{ capability with id := state.destinations.size, start := start },
                        .staged storageId state.storage.size, .limited capacity slotBytes, .receiver,
                        .open 0, writeEnd, rollbackEnd, none, none⟩
                    events := state.events ++ [.begin state.destinations.size, .stage state.destinations.size] } := by
                intro start writeEnd rollbackEnd storage size
                exact ownershipSourceExtension_push state _
              repeat' first
                | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                    reserveStorage, lookupStorage_result, DestinationBacking.writeStorage,
                    Array.getElem?_push_size, Nat.lt_irrefl,
                    replaceStorage_result, Array.size_push, Nat.lt_succ_self, emit_result,
                    ↓reduceIte, bind, pure, ConstructionResult.finalState, List.append_assoc]
                | source_allocation_split_if
                | exact .refl state
                | exact reservedFrame
                | exact allocated _ _ _ _ (by simp [reserved])

end Goose.Proofs.ConstructionExecutionOwnership
