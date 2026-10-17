import Goose.Proofs.ConstructionExecutionProtocolDestination
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

local syntax "protocol_split_if" : tactic
elab_rules : tactic
  | `(tactic| protocol_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no construction condition to split"
      return [yes.mvarId, no.mvarId]

private theorem replace_lifecycle (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (events : List ConstructionEvent)
    (present : state.destinations[id]? = some before)
    (capability : after.capability.id = before.capability.id)
    (backing : after.backing = before.backing) (use : after.use = before.use)
    (other : ∀ index, index ≠ id → destinationObservations index events = [])
    (transition : ∀ phase, phase.matchesDestination before → ∃ next,
      runDestinationTrace id phase events = some next ∧ next.matchesDestination after)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with destinations := state.destinations.set! id after, events := state.events ++ events } := by
  refine ⟨destinationTraceProtocol_replace state id before after events present other transition valid.1,
    ?_, ?_, destinationOwnersOrdered_replace state id before after present use valid.2.2.2⟩
  · intro index destination found
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at found
    by_cases same : id = index
    · subst index
      have inside := (Array.getElem?_eq_some_iff.mp present).choose
      simp only [inside, ↓reduceIte, Option.some.injEq] at found
      subst destination
      exact capability.trans (valid.2.1 id before present)
    · exact valid.2.1 index destination (by simpa only [same, ↓reduceIte] using found)
  · have references := valid.2.2.1 id before present
    apply destinationStorageReferences_replace state id after state.storage (Nat.le_refl _)
    · simpa only [PendingDestination.storage, backing] using references.1
    · simpa only [backing] using references.2
    · exact valid.2.2.1

private theorem replace_silent_lifecycle (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (capability : after.capability.id = before.capability.id)
    (backing : after.backing = before.backing) (use : after.use = before.use)
    (progress : after.progress = before.progress)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with destinations := state.destinations.set! id after } := by
  simpa using replace_lifecycle state id before after [] present capability backing use
    (by intro index different; rfl)
    (by
      intro phase matched
      exact ⟨phase, rfl, by simpa only [DestinationTracePhase.matchesDestination,
        progress, backing] using matched⟩) valid

private theorem write_commit_lifecycle (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (count : Nat) (bytes : ByteArray)
    (storage : Array ReceivingStorage) (size : storage.size = state.storage.size)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .open count)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with storage := storage, destinations := state.destinations.set! id { destination with progress := .open (count + 1), writeEnd := destination.writeEnd + bytes.size }, events := state.events ++ [.write id count] } := by
  exact replace_lifecycle { state with storage := storage } id destination _ [.write id count]
    present rfl rfl rfl
    (by intro index different; simp [destinationObservations, observeDestination, Ne.symm different])
    (fun phase matched => write_destination_trace_transition id count destination progress bytes phase matched)
    (destinationLifecycleInvariant_storage_frame state storage size valid)

private theorem finish_commit_lifecycle (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (count : Nat)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .open count)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with destinations := state.destinations.set! id { destination with progress := .built count } } := by
  simpa using replace_lifecycle state id destination { destination with progress := .built count } [] present rfl rfl rfl
    (by intro index different; rfl)
    (fun phase matched => ⟨phase, rfl,
      finish_destination_trace_transition destination count progress phase matched⟩) valid

private theorem remove_header_commit_lifecycle (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (count : Nat)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built count)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with destinations := state.destinations.set! id { destination with layout := .elements, writeEnd := destination.writeEnd - 4 }, events := state.events ++ [.relocate id .headerRemoval] } := by
  apply replace_lifecycle state id destination { destination with layout := .elements, writeEnd := destination.writeEnd - 4 } [.relocate id .headerRemoval] present rfl rfl rfl
    (by intro index different; simp [destinationObservations, observeDestination, Ne.symm different])
    _ valid
  intro phase matched
  cases phase <;>
    simp_all [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress,
      runDestinationTrace, destinationObservations, observeDestination,
      runDestinationObservations, destinationTraceStep]

private theorem truncate_commit_lifecycle (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (oldCount count finish : Nat)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built oldCount)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with destinations := state.destinations.set! id { destination with progress := .built count, writeEnd := finish } } := by
  simpa using replace_lifecycle state id destination { destination with progress := .built count, writeEnd := finish } [] present rfl rfl rfl
    (by intro index different; rfl)
    (by
      intro phase matched
      exact ⟨phase, rfl, by cases phase <;>
        simp_all [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress]⟩)
    valid

theorem adaptDestinationType_destination_lifecycle_invariant (id : DestinationId)
    (logicalType : Construct.Ty) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (adaptDestinationType id logicalType state).finalState := by
  simp only [adaptDestinationType, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact valid
          all_goals
            try simp only [pure, bind]
            protocol_split_if
            · exact valid
            · simp only [replaceDestination_result, inside, ↓reduceIte, ConstructionResult.finalState]
              exact replace_silent_lifecycle state id destination _ present rfl rfl rfl (by simp only [progress]) valid

theorem restoreReceivingLayout_destination_lifecycle_invariant (id : DestinationId)
    (layout : ReceivingLayout) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (restoreReceivingLayout id layout state).finalState := by
  simp only [restoreReceivingLayout, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact valid
          case built count =>
            try simp only [pure, bind]
            protocol_split_if
            · exact valid
            · simp only [replaceDestination_result, inside, ↓reduceIte, ConstructionResult.finalState]
              exact replace_silent_lifecycle state id destination _ present rfl rfl rfl (by simp only [progress]) valid

theorem finishDestination_destination_lifecycle_invariant (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (finishDestination id state).finalState := by
  simp only [finishDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have bound := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact valid
          case «open» count =>
            have finished := finish_commit_lifecycle state id destination count present progress valid
            have storedFinished : ∀ storage : ReceivingStorage,
                DestinationLifecycleInvariant { state with storage := state.storage.set! destination.storage storage, destinations := state.destinations.set! id { destination with progress := .built count } } := by
              intro storage
              exact finish_commit_lifecycle { state with storage := state.storage.set! destination.storage storage }
                id destination count present progress
                (destinationLifecycleInvariant_storage_frame state _ (by simp) valid)
            cases layout : destination.layout <;> simp only [layout]
            all_goals
              simp only [layout] at finished storedFinished
              cases stored : state.storage[destination.storage]?
              all_goals
                repeat' first
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                      ConstructionM.fail, ConstructionResult.finalState]
                  | protocol_split_if
                  | exact valid
                  | exact finished
                  | exact storedFinished _

theorem removeConstructionHeader_destination_lifecycle_invariant (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (removeConstructionHeader id state).finalState := by
  simp only [removeConstructionHeader, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have bound := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact valid
          case built count =>
            have removed : ∀ storage : ReceivingStorage,
                DestinationLifecycleInvariant { state with storage := state.storage.set! destination.storage storage, destinations := state.destinations.set! id { destination with layout := .elements, writeEnd := destination.writeEnd - 4 }, events := state.events ++ [.relocate id .headerRemoval] } := by
              intro storage
              exact remove_header_commit_lifecycle { state with storage := state.storage.set! destination.storage storage }
                id destination count present progress
                (destinationLifecycleInvariant_storage_frame state _ (by simp) valid)
            simp only [progress] at removed
            cases stored : state.storage[destination.storage]?
            all_goals
              repeat' first
                | simp only [lookupStorage_result, stored, replaceStorage_result,
                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                | protocol_split_if
                | exact valid
                | exact removed _

theorem prepareNamedBinding_destination_lifecycle_invariant (id : DestinationId)
    (localType : Construct.Ty) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (prepareNamedBinding id localType state).finalState := by
  simp only [prepareNamedBinding, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have bound := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact valid
          case «open» count =>
            cases count <;> try exact valid
            case zero =>
              have prepared : ∀ (storage : Array ReceivingStorage), storage.size = state.storage.size →
                  ∀ (layout : ReceivingLayout) (writeEnd : Nat),
                  DestinationLifecycleInvariant { state with storage := storage, destinations := state.destinations.set! id { destination with capability := { destination.capability with logicalType := localType }, layout := layout, writeEnd := writeEnd } } := by
                intro storage size layout writeEnd
                exact replace_silent_lifecycle { state with storage := storage } id destination _
                  present rfl rfl rfl rfl
                  (destinationLifecycleInvariant_storage_frame state storage size valid)
              simp only [progress] at prepared
              cases stored : state.storage[destination.storage]?
              all_goals
                repeat' first
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                      ConstructionM.fail, emit_result, ConstructionResult.finalState]
                  | protocol_split_if
                  | exact valid
                  | exact prepared _ (by simp) _ _

end Goose.Proofs.ConstructionExecutionProtocol
