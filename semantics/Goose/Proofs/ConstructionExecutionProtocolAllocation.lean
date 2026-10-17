import Goose.Proofs.ConstructionExecutionProtocolDestination
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

private theorem suspend_matches (parent : PendingDestination) (count child : Nat)
    (progress : parent.progress = .open count ∨ parent.progress = .built count)
    (phase : DestinationTracePhase) (matched : phase.matchesDestination parent) :
    phase.matchesDestination { parent with progress := .suspended count child } := by
  rcases progress with progress | progress <;> cases phase <;>
    simp_all [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress]

theorem destinationLifecycleInvariant_allocate_child (state : ConstructionState) (parentId : DestinationId)
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
    DestinationLifecycleInvariant { state with
      storage := storage
      destinations := (state.destinations.push child).set! parentId
        { parent with progress := .suspended count state.destinations.size }
      events := state.events ++ events } := by
  have inside := (Array.getElem?_eq_some_iff.mp present).choose
  let allocated : ConstructionState := { state with
    storage := storage, destinations := state.destinations.push child, events := state.events ++ events }
  have allocatedValid : DestinationLifecycleInvariant allocated := by
    exact destinationLifecycleInvariant_push state child events storage size correct writeStorage receiverStorage
      (by simpa only [use] using inside) other initial valid
  have parentPresent : allocated.destinations[parentId]? = some parent := by
    simpa only [allocated, Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using present
  exact destinationLifecycleInvariant_replace_silent allocated parentId parent _ storage parentPresent rfl
    rfl rfl rfl (suspend_matches parent count state.destinations.size progress) allocatedValid

theorem openChild_destination_lifecycle_invariant (parentId : DestinationId) (logicalType : Construct.Ty)
    (layout : ReceivingLayout) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (openChild parentId logicalType layout state).finalState := by
  simp only [openChild, writableDestination_result, bind]
  cases present : state.destinations[parentId]? with
  | none => exact valid
  | some parent =>
      simp only [present]
      cases allowed : destinationCanWrite state parentId with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have insideAfter := Nat.lt_succ_of_lt inside
          have storageInside := (valid.2.2.1 parentId parent present).1
          cases progress : parent.progress <;> try simp only [progress] <;> try exact valid
          case «open» count =>
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => exact valid
            | some receiving =>
                simp only [stored]
                repeat' first
                  | exact valid
                  | solve
                    | apply destinationLifecycleInvariant_allocate_child state parentId parent _ count
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

end Goose.Proofs.ConstructionExecutionProtocol
