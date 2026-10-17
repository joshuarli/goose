import Goose.Construct.DestinationTrace
import Goose.Proofs.ConstructionExecutionProtocolKernel

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem destinationCapabilities_push (state : ConstructionState) (destination : PendingDestination)
    (correct : destination.capability.id = state.destinations.size)
    (valid : DestinationCapabilitiesIndexed state) :
    DestinationCapabilitiesIndexed { state with destinations := state.destinations.push destination } := by
  intro index current present
  rw [Array.getElem?_push] at present
  by_cases same : index = state.destinations.size
  · simp only [same, ↓reduceIte, Option.some.injEq] at present
    subst current
    exact correct.trans same.symm
  · exact valid index current (by simpa only [same, ↓reduceIte] using present)

theorem destinationCapabilities_replace (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (correct : destination.capability.id = id)
    (valid : DestinationCapabilitiesIndexed state) :
    DestinationCapabilitiesIndexed { state with destinations := state.destinations.set! id destination } := by
  intro index current present
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at present
  by_cases same : id = index
  · subst index
    by_cases inside : id < state.destinations.size
    · simp only [inside, ↓reduceIte, Option.some.injEq] at present
      subst current
      exact correct
    · simp [inside] at present
  · exact valid index current (by simpa only [same, ↓reduceIte] using present)

theorem destinationOwnersOrdered_push (state : ConstructionState) (destination : PendingDestination)
    (ordered : match destination.use with
      | .receiver => True
      | .child owner | .replacement owner => owner < state.destinations.size)
    (valid : DestinationOwnersOrdered state) :
    DestinationOwnersOrdered { state with destinations := state.destinations.push destination } := by
  intro index current present
  rw [Array.getElem?_push] at present
  by_cases same : index = state.destinations.size
  · simp only [same, ↓reduceIte, Option.some.injEq] at present
    subst current
    cases use : destination.use <;> simpa only [same, use] using ordered
  · exact valid index current (by simpa only [same, ↓reduceIte] using present)

theorem destinationOwnersOrdered_replace (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (use : after.use = before.use) (valid : DestinationOwnersOrdered state) :
    DestinationOwnersOrdered { state with destinations := state.destinations.set! id after } := by
  intro index destination found
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at found
  by_cases same : id = index
  · subst index
    by_cases inside : id < state.destinations.size
    · simp only [inside, ↓reduceIte, Option.some.injEq] at found
      subst destination
      simpa only [use] using valid id before present
    · simp [inside] at found
  · exact valid index destination (by simpa only [same, ↓reduceIte] using found)

theorem destinationStorageReferences_replace (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (storage : Array ReceivingStorage)
    (size : state.storage.size ≤ storage.size)
    (writeStorage : destination.storage < storage.size)
    (receiverStorage : destination.backing.receiverStorage < storage.size)
    (valid : DestinationStorageReferencesValid state) :
    DestinationStorageReferencesValid { state with
      destinations := state.destinations.set! id destination, storage := storage } := by
  intro index current present
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at present
  by_cases same : id = index
  · subst index
    by_cases inside : id < state.destinations.size
    · simp only [inside, ↓reduceIte, Option.some.injEq] at present
      subst current
      exact ⟨writeStorage, receiverStorage⟩
    · simp [inside] at present
  · have references := valid index current (by simpa only [same, ↓reduceIte] using present)
    exact ⟨Nat.lt_of_lt_of_le references.1 size, Nat.lt_of_lt_of_le references.2 size⟩

theorem destinationStorageReferences_push (state : ConstructionState)
    (destination : PendingDestination) (storage : Array ReceivingStorage)
    (size : state.storage.size ≤ storage.size)
    (writeStorage : destination.storage < storage.size)
    (receiverStorage : destination.backing.receiverStorage < storage.size)
    (valid : DestinationStorageReferencesValid state) :
    DestinationStorageReferencesValid { state with
      destinations := state.destinations.push destination, storage := storage } := by
  intro index current present
  rw [Array.getElem?_push] at present
  by_cases same : index = state.destinations.size
  · simp only [same, ↓reduceIte, Option.some.injEq] at present
    subst current
    exact ⟨writeStorage, receiverStorage⟩
  · have references := valid index current (by simpa only [same, ↓reduceIte] using present)
    exact ⟨Nat.lt_of_lt_of_le references.1 size, Nat.lt_of_lt_of_le references.2 size⟩

theorem destinationTraceProtocol_push (state : ConstructionState)
    (destination : PendingDestination) (events : List ConstructionEvent)
    (other : ∀ index, index ≠ state.destinations.size → destinationObservations index events = [])
    (transition : ∃ phase,
      runDestinationTrace state.destinations.size .unseen events = some phase ∧
        phase.matchesDestination destination)
    (valid : DestinationTraceProtocol state) :
    DestinationTraceProtocol { state with
      destinations := state.destinations.push destination, events := state.events ++ events } := by
  intro index
  change match (state.destinations.push destination)[index]? with
    | none => runDestinationTrace index .unseen (state.events ++ events) = some .unseen
    | some destination => ∃ phase,
        runDestinationTrace index .unseen (state.events ++ events) = some phase ∧
        phase.matchesDestination destination
  by_cases same : index = state.destinations.size
  · subst index
    simp only [Array.getElem?_push_size]
    have unseen : runDestinationTrace state.destinations.size .unseen state.events = some .unseen := by
      have previous := valid state.destinations.size
      simpa only [Array.getElem?_size] using previous
    obtain ⟨phase, accepted, matched⟩ := transition
    refine ⟨phase, ?_, matched⟩
    rw [runDestinationTrace_append, unseen]
    simpa using accepted
  · have traceUnchanged : runDestinationTrace index .unseen (state.events ++ events) =
        runDestinationTrace index .unseen state.events := by
      rw [runDestinationTrace_append]
      simp only [runDestinationTrace, other index same, runDestinationObservations]
      cases runDestinationObservations .unseen (destinationObservations index state.events) <;> rfl
    cases observed : state.destinations[index]? <;>
      simpa only [Array.getElem?_push, same, ↓reduceIte, traceUnchanged, observed] using valid index

theorem destinationTraceProtocol_replace (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (events : List ConstructionEvent)
    (present : state.destinations[id]? = some before)
    (other : ∀ index, index ≠ id → destinationObservations index events = [])
    (transition : ∀ phase, phase.matchesDestination before → ∃ next,
      runDestinationTrace id phase events = some next ∧ next.matchesDestination after)
    (valid : DestinationTraceProtocol state) :
    DestinationTraceProtocol { state with
      destinations := state.destinations.set! id after, events := state.events ++ events } := by
  have inside := (Array.getElem?_eq_some_iff.mp present).choose
  intro index
  change match (state.destinations.set! id after)[index]? with
    | none => runDestinationTrace index .unseen (state.events ++ events) = some .unseen
    | some destination => ∃ phase,
        runDestinationTrace index .unseen (state.events ++ events) = some phase ∧
        phase.matchesDestination destination
  by_cases same : id = index
  · subst index
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside]
    have previous := valid id
    rw [present] at previous
    obtain ⟨phase, accepted, matched⟩ := previous
    obtain ⟨next, continued, matchedNext⟩ := transition phase matched
    refine ⟨next, ?_, matchedNext⟩
    rw [runDestinationTrace_append, accepted]
    simpa using continued
  · have traceUnchanged : runDestinationTrace index .unseen (state.events ++ events) =
        runDestinationTrace index .unseen state.events := by
      rw [runDestinationTrace_append]
      simp only [runDestinationTrace, other index (Ne.symm same), runDestinationObservations]
      cases runDestinationObservations .unseen (destinationObservations index state.events) <;> rfl
    cases observed : state.destinations[index]? <;>
      simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same,
        traceUnchanged, observed] using valid index

theorem stage_destination_trace_transition (id receiver stage : Nat)
    (destination : PendingDestination) (progress : destination.progress = .open 0)
    (backing : destination.backing = .direct receiver)
    (receiving : destination.use = .receiver)
    (phase : DestinationTracePhase) (valid : phase.matchesDestination destination) :
    ∃ next, runDestinationTrace id phase [.stage id] = some next ∧
      next.matchesDestination { destination with
        backing := .staged receiver stage
        capability := { destination.capability with start := 0 }
        writeEnd := 0, rollbackEnd := 0 } := by
  cases phase with
  | unseen | published | abandoned =>
      simp [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress,
        progress] at valid
  | live staged wrote =>
      simp only [DestinationTracePhase.matchesDestination, progress, backing, receiving,
        DestinationTracePhase.matchesProgress, true_and] at valid
      obtain ⟨rfl, rfl⟩ := valid
      exact ⟨.live true false, by simp [runDestinationTrace, destinationObservations,
        observeDestination, runDestinationObservations, destinationTraceStep], by
        simp [DestinationTracePhase.matchesDestination,
          DestinationTracePhase.matchesProgress, progress, receiving]⟩

theorem write_destination_trace_transition (id : DestinationId) (count : Nat)
    (destination : PendingDestination) (progress : destination.progress = .open count)
    (bytes : ByteArray) (phase : DestinationTracePhase)
    (valid : phase.matchesDestination destination) :
    ∃ next, runDestinationTrace id phase [.write id count] = some next ∧
      next.matchesDestination { destination with
        progress := .open (count + 1)
        writeEnd := destination.writeEnd + bytes.size } := by
  cases phase with
  | unseen | published | abandoned =>
      simp [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress,
        progress] at valid
  | live staged wrote =>
      exact ⟨.live staged true, by simp [runDestinationTrace, destinationObservations,
        observeDestination, runDestinationObservations, destinationTraceStep], by
        cases count <;> cases destination.backing <;>
          simp [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress]⟩

theorem finish_destination_trace_transition (destination : PendingDestination) (count : Nat)
    (progress : destination.progress = .open count) (phase : DestinationTracePhase)
    (valid : phase.matchesDestination destination) :
    phase.matchesDestination { destination with progress := .built count } := by
  cases phase <;>
    simp_all [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress]

theorem destinationTraceProtocol_replace_silent (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (transition : ∀ phase : DestinationTracePhase,
      phase.matchesDestination before → phase.matchesDestination after)
    (valid : DestinationTraceProtocol state) :
    DestinationTraceProtocol { state with destinations := state.destinations.set! id after } := by
  simpa using destinationTraceProtocol_replace state id before after [] present
    (by intro index different; rfl)
    (by intro phase matched; exact ⟨phase, rfl, transition phase matched⟩) valid

theorem destinationTraceProtocol_emit (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (events : List ConstructionEvent)
    (present : state.destinations[id]? = some destination)
    (other : ∀ index, index ≠ id → destinationObservations index events = [])
    (transition : ∀ phase, phase.matchesDestination destination → ∃ next,
      runDestinationTrace id phase events = some next ∧ next.matchesDestination destination)
    (valid : DestinationTraceProtocol state) :
    DestinationTraceProtocol { state with events := state.events ++ events } := by
  intro index
  by_cases same : index = id
  · subst index
    have previous := valid id
    rw [present] at previous
    obtain ⟨phase, accepted, matched⟩ := previous
    obtain ⟨next, continued, matchedNext⟩ := transition phase matched
    simp only [present]
    refine ⟨next, ?_, matchedNext⟩
    rw [runDestinationTrace_append, accepted]
    simpa using continued
  · have traceUnchanged : runDestinationTrace index .unseen (state.events ++ events) =
        runDestinationTrace index .unseen state.events := by
      rw [runDestinationTrace_append]
      simp only [runDestinationTrace, other index same, runDestinationObservations]
      cases runDestinationObservations .unseen (destinationObservations index state.events) <;> rfl
    simpa only [traceUnchanged] using valid index

theorem copy_destination_trace_transition (id : DestinationId) (source : CopySource)
    (destination : PendingDestination) (count : Nat) (progress : destination.progress = .open count)
    (phase : DestinationTracePhase) (valid : phase.matchesDestination destination) :
    runDestinationTrace id phase [.copy source id] = some phase := by
  cases phase with
  | unseen | published | abandoned =>
      simp [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress,
        progress] at valid
  | live staged wrote =>
      simp [runDestinationTrace, destinationObservations, observeDestination,
        runDestinationObservations, destinationTraceStep]

theorem destinationLifecycleInvariant_push (state : ConstructionState)
    (destination : PendingDestination) (events : List ConstructionEvent) (storage : Array ReceivingStorage)
    (size : storage.size = state.storage.size)
    (correct : destination.capability.id = state.destinations.size)
    (writeStorage : destination.storage < state.storage.size)
    (receiverStorage : destination.backing.receiverStorage < state.storage.size)
    (ordered : match destination.use with
      | .receiver => True
      | .child owner | .replacement owner => owner < state.destinations.size)
    (other : ∀ index, index ≠ state.destinations.size → destinationObservations index events = [])
    (transition : ∃ phase,
      runDestinationTrace state.destinations.size .unseen events = some phase ∧
        phase.matchesDestination destination)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with
      destinations := state.destinations.push destination
      events := state.events ++ events
      storage := storage } := by
  refine ⟨destinationTraceProtocol_push state destination events other transition valid.1,
    destinationCapabilities_push state destination correct valid.2.1, ?_,
    destinationOwnersOrdered_push state destination ordered valid.2.2.2⟩
  apply destinationStorageReferences_push state destination storage
  · omega
  · simpa only [size] using writeStorage
  · simpa only [size] using receiverStorage
  · exact valid.2.2.1

theorem destinationLifecycleInvariant_replace_silent (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (storage : Array ReceivingStorage)
    (present : state.destinations[id]? = some before)
    (size : storage.size = state.storage.size)
    (capability : after.capability.id = before.capability.id)
    (backing : after.backing = before.backing) (use : after.use = before.use)
    (transition : ∀ phase : DestinationTracePhase,
      phase.matchesDestination before → phase.matchesDestination after)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with
      destinations := state.destinations.set! id after, storage := storage } := by
  refine ⟨destinationTraceProtocol_replace_silent state id before after present transition valid.1,
    destinationCapabilities_replace state id after
      (capability.trans (valid.2.1 id before present)) valid.2.1, ?_,
    destinationOwnersOrdered_replace state id before after present use valid.2.2.2⟩
  apply destinationStorageReferences_replace state id after storage
  · omega
  · simpa only [PendingDestination.storage, backing, size] using
      (valid.2.2.1 id before present).1
  · simpa only [backing, size] using (valid.2.2.1 id before present).2
  · exact valid.2.2.1

end Goose.Proofs.ConstructionExecutionProtocol
