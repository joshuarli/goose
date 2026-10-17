import Goose.Proofs.ConstructionExecutionProtocolDestination

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private theorem abandon_trace_transition (id : DestinationId) (destination : PendingDestination)
    (active : ∃ count, destination.progress = .open count ∨ destination.progress = .built count)
    (phase : DestinationTracePhase) (valid : phase.matchesDestination destination) :
    ∃ next, runDestinationTrace id phase [.abandon id] = some next ∧
      next.matchesDestination { destination with progress := .abandoned } := by
  have live : ∃ staged wrote, phase = .live staged wrote := by
    cases phase with
    | live staged wrote => exact ⟨staged, wrote, rfl⟩
    | unseen | published | abandoned =>
        obtain ⟨count, progress | progress⟩ := active <;>
          simp [DestinationTracePhase.matchesDestination,
            DestinationTracePhase.matchesProgress, progress] at valid
  obtain ⟨staged, wrote, rfl⟩ := live
  exact ⟨.abandoned, by simp [runDestinationTrace, destinationObservations, observeDestination,
    runDestinationObservations, destinationTraceStep], by simp [DestinationTracePhase.matchesDestination,
    DestinationTracePhase.matchesProgress]⟩

private theorem abandon_update_parts (id : DestinationId) (state : ConstructionState)
    (destination : PendingDestination) (storage : Array ReceivingStorage)
    (present : state.destinations[id]? = some destination)
    (active : ∃ count, destination.progress = .open count ∨ destination.progress = .built count)
    (size : storage.size = state.storage.size) (valid : DestinationLifecycleInvariant state) :
    let after := { state with
      storage := storage
      destinations := state.destinations.set! id { destination with progress := .abandoned }
      events := state.events ++ [.abandon id] }
    DestinationTraceProtocol after ∧ DestinationStorageReferencesValid after ∧
      DestinationOwnersOrdered after := by
  refine ⟨?_, ?_, ?_⟩
  · exact destinationTraceProtocol_replace state id destination _ [.abandon id] present
      (by intro index different; simp [destinationObservations, observeDestination, Ne.symm different])
      (abandon_trace_transition id destination active) valid.1
  · apply destinationStorageReferences_replace state id _ storage
    · omega
    · simpa only [size, PendingDestination.storage] using (valid.2.2.1 id destination present).1
    · simpa only [size] using (valid.2.2.1 id destination present).2
    · exact valid.2.2.1
  · exact destinationOwnersOrdered_replace state id destination _ present rfl valid.2.2.2

private theorem abandonDestination_lifecycle_parts (id : DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    DestinationTraceProtocol (abandonDestination id state).finalState ∧
      DestinationStorageReferencesValid (abandonDestination id state).finalState ∧
      DestinationOwnersOrdered (abandonDestination id state).finalState := by
  simp only [abandonDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact ⟨valid.1, valid.2.2.1, valid.2.2.2⟩
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact ⟨valid.1, valid.2.2.1, valid.2.2.2⟩
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have storageInside := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> try simp only [progress] <;>
            try exact ⟨valid.1, valid.2.2.1, valid.2.2.2⟩
          all_goals
            have active : ∃ count,
                destination.progress = .open count ∨ destination.progress = .built count := by
              first | exact ⟨_, Or.inl progress⟩ | exact ⟨_, Or.inr progress⟩
            simp only [lookupStorage_result, bind]
            cases state.storage[destination.storage]? <;>
              simp only [bind, replaceStorage_result, replaceDestination_result, storageInside,
                inside, ↓reduceIte, emit_result, ConstructionResult.finalState]
            · exact ⟨valid.1, valid.2.2.1, valid.2.2.2⟩
            · apply abandon_update_parts id state destination _ present active
              · simp [Array.set!_eq_setIfInBounds]
              · exact valid

theorem abandonDestination_destination_lifecycle_invariant (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (abandonDestination id state).finalState := by
  have parts := abandonDestination_lifecycle_parts id state valid
  exact ⟨parts.1, abandonDestination_destination_capabilities id state valid.2.1,
    parts.2.1, parts.2.2⟩

end Goose.Proofs.ConstructionExecutionProtocol
