import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataUpdates
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

local syntax "allocation_split_if" : tactic
elab_rules : tactic
  | `(tactic| allocation_split_if) =>
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.splitIfTarget? goal
          | Lean.throwError "no allocation condition to split"
        return [yes.mvarId, no.mvarId]

private theorem metadata_allocate_child (state : ConstructionState) (parentId : DestinationId)
    (parent child : PendingDestination) (count : Nat) (events : List ConstructionEvent)
    (storage : Array ReceivingStorage) (size : storage.size = state.storage.size)
    (present : state.destinations[parentId]? = some parent)
    (progress : parent.progress = .open count ∨ parent.progress = .built count)
    (correct : child.capability.id = state.destinations.size)
    (use : child.use = .child parentId)
    (writeStorage : child.storage < state.storage.size)
    (receiverStorage : child.backing.receiverStorage < state.storage.size)
    (other : ∀ index, index ≠ state.destinations.size → destinationObservations index events = [])
    (initial : ∃ phase,
      runDestinationTrace state.destinations.size .unseen events = some phase ∧
        phase.matchesDestination child)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state { state with
      storage := storage
      destinations := (state.destinations.push child).set! parentId
        { parent with progress := .suspended count state.destinations.size }
      events := state.events ++ events } := by
  have inside := (Array.getElem?_eq_some_iff.mp present).choose
  let allocated : ConstructionState := { state with
    storage := storage, destinations := state.destinations.push child, events := state.events ++ events }
  have frame : ReservationMetadataFrame state allocated := by
    apply reservationMetadataFrame_push state child storage events (Nat.le_of_eq size.symm)
    intro queried bound
    exact other queried (Nat.ne_of_lt bound)
  have parentPresent : allocated.destinations[parentId]? = some parent := by
    simpa only [allocated, Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using present
  have changed : ReservationMetadataFrame allocated { allocated with
      storage := storage
      destinations := allocated.destinations.set! parentId { parent with progress := .suspended count state.destinations.size } } := by
    simpa only [List.append_nil] using reservationMetadataFrame_replace_mutable allocated parentId parent { parent with progress := .suspended count state.destinations.size }
      storage [] parentPresent (Nat.le_refl _) (by intro stable; rcases progress with h | h <;> simp [h, ReservationStableProgress] at stable) (by intro queried different; rfl)
  exact frame.trans changed

private theorem metadata_allocate_replacement (state : ConstructionState) (parentId : DestinationId)
    (parent child : PendingDestination) (count : Nat) (storage : Array ReceivingStorage)
    (size : storage.size = state.storage.size)
    (present : state.destinations[parentId]? = some parent)
    (progress : parent.progress = .open count ∨ parent.progress = .built count ∨
      ∃ nested, parent.progress = .suspended count nested)
    (correct : child.capability.id = state.destinations.size)
    (use : child.use = .replacement parentId)
    (writeStorage : child.storage < state.storage.size)
    (receiverStorage : child.backing.receiverStorage < state.storage.size)
    (initial : ∃ phase,
      runDestinationTrace state.destinations.size .unseen [.begin state.destinations.size] = some phase ∧
        phase.matchesDestination child)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state { state with
      storage := storage
      destinations := (state.destinations.push child).set! parentId
        { parent with progress := .exiting count state.destinations.size }
      events := state.events ++ [.begin state.destinations.size] } := by
  have inside := (Array.getElem?_eq_some_iff.mp present).choose
  let allocated : ConstructionState := { state with
    storage := storage, destinations := state.destinations.push child, events := state.events ++ [.begin state.destinations.size] }
  have frame : ReservationMetadataFrame state allocated := by
    apply reservationMetadataFrame_push state child storage [.begin state.destinations.size] (Nat.le_of_eq size.symm)
    intro queried bound
    simp [destinationObservations, observeDestination, Nat.ne_of_lt bound, Nat.ne_of_lt bound |>.symm]
  have parentPresent : allocated.destinations[parentId]? = some parent := by
    simpa only [allocated, Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using present
  have changed : ReservationMetadataFrame allocated { allocated with
      storage := storage
      destinations := allocated.destinations.set! parentId { parent with progress := .exiting count state.destinations.size } } := by
    simpa only [List.append_nil] using reservationMetadataFrame_replace_mutable allocated parentId parent { parent with progress := .exiting count state.destinations.size }
      storage [] parentPresent (Nat.le_refl _) (by intro stable; rcases progress with h | h | ⟨nested, h⟩ <;> simp [h, ReservationStableProgress] at stable) (by intro queried different; rfl)
  exact frame.trans changed

theorem openChild_reservation_frame (parentId : DestinationId) (logicalType : Construct.Ty)
    (layout : ReceivingLayout) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (openChild parentId logicalType layout state).finalState := by
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
                    | apply metadata_allocate_child state parentId parent _ count
                        [.begin state.destinations.size] _
                      · simp [Array.set!_eq_setIfInBounds]
                      · exact present
                      · exact Or.inl progress
                      · rfl
                      · rfl
                      · simpa only [PendingDestination.storage, DestinationBacking.writeStorage] using storageInside
                      · simpa only [DestinationBacking.receiverStorage] using storageInside
                      · intro index different
                        simp [destinationObservations, observeDestination, Ne.symm different]
                      · refine ⟨.live false false, ?_, ?_⟩
                        · simp [runDestinationTrace, destinationObservations, observeDestination,
                            runDestinationObservations, destinationTraceStep]
                        · simp [DestinationTracePhase.matchesDestination,
                            DestinationTracePhase.matchesProgress]
                      · exact valid
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      replaceDestination_result, replaceStorage_result, emit_result,
                      Array.size_push, insideAfter, storageInside, ↓reduceIte,
                      bind, pure, ConstructionResult.finalState]
                  | allocation_split_if
                  | split

theorem openElementExtension_reservation_frame (parentId : DestinationId) (logicalType : Construct.Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) (receiverLoc : Core.Loc) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (openElementExtension parentId logicalType layout knownCount receiverLoc state).finalState := by
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
                      apply metadata_allocate_child state parentId parent _ count
                        [.begin state.destinations.size] _
                      · simp [Array.set!_eq_setIfInBounds]
                      · exact present
                      · exact Or.inr progress
                      · rfl
                      · rfl
                      · simpa only [PendingDestination.storage, DestinationBacking.writeStorage] using storageInside
                      · simpa only [DestinationBacking.receiverStorage] using storageInside
                      · intro index different
                        simp [destinationObservations, observeDestination, Ne.symm different]
                      · refine ⟨.live false false, ?_, ?_⟩
                        · simp [runDestinationTrace, destinationObservations, observeDestination,
                            runDestinationObservations, destinationTraceStep]
                        · simp [DestinationTracePhase.matchesDestination,
                            DestinationTracePhase.matchesProgress]
                      · exact valid
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      replaceDestination_result, replaceStorage_result, emit_result,
                      Array.size_push, insideAfter, storageInside, stored, parentLayout, parentBacking, ↓reduceIte,
                      bind, pure, ConstructionResult.finalState]
                  | allocation_split_if
                  | split


theorem openExitReplacement_reservation_frame (parentId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (openExitReplacement parentId state).finalState := by
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
                    | first
                      | apply metadata_allocate_replacement state parentId parent _ _ _ _ present (Or.inl progress)
                      | apply metadata_allocate_replacement state parentId parent _ _ _ _ present (Or.inr (Or.inl progress))
                      | apply metadata_allocate_replacement state parentId parent _ _ _ _ present (Or.inr (Or.inr ⟨_, progress⟩))
                      · rfl
                      · rfl
                      · exact storageInside
                      · exact (valid.2.2.1 parentId parent present).2
                      · refine ⟨.live false false, ?_, ?_⟩
                        · simp [runDestinationTrace, destinationObservations, observeDestination,
                            runDestinationObservations, destinationTraceStep]
                        · simp [DestinationTracePhase.matchesDestination,
                            DestinationTracePhase.matchesProgress]
                      · exact valid
                      · simp [Array.set!_eq_setIfInBounds]
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      replaceDestination_result, replaceStorage_result, emit_result,
                      Array.size_push, insideAfter, storageInside, ↓reduceIte,
                      bind, pure, ConstructionResult.finalState]
                  | allocation_split_if
                  | split


set_option maxHeartbeats 2000000 in
theorem openExtension_reservation_frame (parentId : DestinationId)
    (request : ConstructionRequest) (knownCount : Option Nat)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (openExtension parentId request knownCount state).finalState := by
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
          have reservedValid : DestinationLifecycleInvariant reserved :=
            reserveStorage_destination_lifecycle_invariant ByteArray.empty 0 state valid
          have reservedFrame : ReservationMetadataFrame state reserved := reserveStorage_reservation_frame ByteArray.empty 0 state
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
                      apply metadata_allocate_child state parentId parent _ count
                        [.begin state.destinations.size] _
                      · rfl
                      · exact present
                      · exact Or.inr progress
                      · rfl
                      · rfl
                      · simpa only [PendingDestination.storage, DestinationBacking.writeStorage] using storageInside
                      · simpa only [DestinationBacking.receiverStorage] using storageInside
                      · intro index different
                        simp [destinationObservations, observeDestination, Ne.symm different]
                      · refine ⟨.live false false, ?_, ?_⟩
                        · simp [runDestinationTrace, destinationObservations, observeDestination,
                            runDestinationObservations, destinationTraceStep]
                        · simp [DestinationTracePhase.matchesDestination,
                            DestinationTracePhase.matchesProgress]
                      · exact valid
                  | solve
                    | simp only [← parentLayout, ← parentBacking]
                      apply reservedFrame.trans
                      apply metadata_allocate_child reserved parentId parent _ count
                        [.begin state.destinations.size, .stage state.destinations.size] _
                      · rfl
                      · exact present
                      · exact Or.inr progress
                      · rfl
                      · rfl
                      · simp [reserved, PendingDestination.storage, DestinationBacking.writeStorage]
                      · simpa only [reserved, Array.size_push, DestinationBacking.receiverStorage]
                          using Nat.lt.step storageInside
                      · intro index different
                        simp only [reserved] at different
                        simp [destinationObservations, observeDestination, Ne.symm different]
                      · refine ⟨.live true false, ?_, ?_⟩
                        · simp [reserved, runDestinationTrace, destinationObservations, observeDestination,
                            runDestinationObservations, destinationTraceStep]
                        · simp [DestinationTracePhase.matchesDestination,
                            DestinationTracePhase.matchesProgress]
                      · exact reservedValid
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      reserveStorage, replaceDestination_result, emit_result,
                      Array.size_push, insideAfter, storageInside, stored, parentLayout, parentBacking,
                      ↓reduceIte, bind, pure, ConstructionResult.finalState, List.append_assoc]
                  | allocation_split_if
                  | split

set_option maxHeartbeats 2000000 in
theorem openDestinationDirect_reservation_frame (storageId : StorageId)
    (capability : Core.Destination Construct.Ty) (layout : ReceivingLayout) (knownCount : Option Nat)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (openDestinationDirect storageId capability layout knownCount state).finalState := by
  rw [openDestinationDirect_transition]
  simp only [lookupStorage_result, bind]
  cases stored : state.storage[storageId]? with
  | none => exact .refl state
  | some receiving =>
      simp only [stored]
      have storageInside := (Array.getElem?_eq_some_iff.mp stored).choose
      have allocated : ∀ (start writeEnd rollbackEnd : Nat) (storage : Array ReceivingStorage),
          storage.size = state.storage.size →
          ReservationMetadataFrame state { state with
            storage := storage
            destinations := state.destinations.push
              ⟨{ capability with id := state.destinations.size, start := start }, .direct storageId,
                layout, .receiver, .open 0, writeEnd, rollbackEnd, knownCount, none⟩
            events := state.events ++ [.begin state.destinations.size] } := by
        intro start writeEnd rollbackEnd storage size
        apply reservationMetadataFrame_push state _ storage _ (Nat.le_of_eq size.symm)
        intro queried inside
        simp [destinationObservations, observeDestination, Nat.ne_of_lt inside, (Nat.ne_of_lt inside).symm]
      cases layout <;> cases knownCount
      all_goals repeat' first
        | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
            lookupStorage_result, stored, DestinationBacking.writeStorage,
            replaceStorage_result, storageInside, emit_result, Nat.lt_irrefl,
            ↓reduceIte, bind, pure, ConstructionResult.finalState]
        | allocation_split_if
        | exact .refl state
        | exact allocated _ _ _ _ (by simp)

set_option maxHeartbeats 2000000 in
theorem openDestination_reservation_frame (storageId : StorageId)
    (capability : Core.Destination Construct.Ty) (layout : ReceivingLayout) (knownCount : Option Nat)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (openDestination storageId capability layout knownCount state).finalState := by
  cases layout with
  | packed =>
      simpa only [openDestination_transition, openDestinationDirect_transition] using
        openDestinationDirect_reservation_frame storageId capability .packed knownCount state valid
  | elements =>
      simpa only [openDestination_transition, openDestinationDirect_transition] using
        openDestinationDirect_reservation_frame storageId capability .elements knownCount state valid
  | fixed expected =>
      simpa only [openDestination_transition, openDestinationDirect_transition] using
        openDestinationDirect_reservation_frame storageId capability (.fixed expected) knownCount state valid
  | limited capacity slotBytes =>
      cases knownCount with
      | some count =>
          simpa only [openDestination_transition, openDestinationDirect_transition] using
            openDestinationDirect_reservation_frame storageId capability
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
              have reservedValid : DestinationLifecycleInvariant reserved :=
                reserveStorage_destination_lifecycle_invariant ByteArray.empty 0 state valid
              have reservedFrame : ReservationMetadataFrame state reserved := reserveStorage_reservation_frame ByteArray.empty 0 state
              have allocated : ∀ (start writeEnd rollbackEnd : Nat) (storage : Array ReceivingStorage),
                  storage.size = reserved.storage.size →
                  ReservationMetadataFrame state { reserved with
                    storage := storage
                    destinations := reserved.destinations.push
                      ⟨{ capability with id := state.destinations.size, start := start },
                        .staged storageId state.storage.size, .limited capacity slotBytes, .receiver,
                        .open 0, writeEnd, rollbackEnd, none, none⟩
                    events := state.events ++ [.begin state.destinations.size, .stage state.destinations.size] } := by
                intro start writeEnd rollbackEnd storage size
                apply reservedFrame.trans
                apply reservationMetadataFrame_push reserved _ storage _ (Nat.le_of_eq size.symm)
                intro queried inside
                simp only [reserved] at inside
                simp [destinationObservations, observeDestination, Nat.ne_of_lt inside, (Nat.ne_of_lt inside).symm]
              repeat' first
                | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                    reserveStorage, lookupStorage_result, DestinationBacking.writeStorage,
                    Array.getElem?_push_size, Nat.lt_irrefl,
                    replaceStorage_result, Array.size_push, Nat.lt_succ_self, emit_result,
                    ↓reduceIte, bind, pure, ConstructionResult.finalState, List.append_assoc]
                | allocation_split_if
                | exact .refl state
                | exact reservedFrame
                | exact allocated _ _ _ _ (by simp [reserved])

end Goose.Proofs.ConstructionExecutionProtocol
