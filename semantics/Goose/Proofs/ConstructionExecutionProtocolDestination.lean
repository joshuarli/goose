import Goose.Construct.DestinationTrace
import Goose.Proofs.ConstructionExecutionProtocolKernel

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

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
      simp only [DestinationTracePhase.matchesDestination, progress, backing,
        DestinationTracePhase.matchesProgress, true_and] at valid
      obtain ⟨rfl, rfl⟩ := valid
      exact ⟨.live true false, by simp [runDestinationTrace, destinationObservations,
        observeDestination, runDestinationObservations, destinationTraceStep], by
        simp [DestinationTracePhase.matchesDestination,
          DestinationTracePhase.matchesProgress, progress]⟩

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

end Goose.Proofs.ConstructionExecutionProtocol
