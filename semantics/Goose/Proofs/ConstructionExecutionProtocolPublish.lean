import Goose.Proofs.ConstructionExecutionProtocolDestination

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private abbrev publicationStep (id : DestinationId) : ConstructionM Unit :=
  (fun {left right : ConstructionM Unit} (_ : left = right) => left) (publishReady_transition id)

private theorem publish_commit_lifecycle (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (count start writeEnd : Nat) (stage : Option StorageId)
    (storage : Array ReceivingStorage) (size : storage.size = state.storage.size)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built count)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with
      storage := storage
      destinations := state.destinations.set! id { destination with
        progress := .published count
        backing := .direct destination.backing.receiverStorage
        capability := { destination.capability with start := start }
        writeEnd := writeEnd }
      events := state.events ++ (match stage with
        | none => [.publish id]
        | some stage => [.copy (.storage stage []) id, .publish id]) } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply destinationTraceProtocol_replace state id destination _ _ present
      (by
        intro index different
        cases stage <;> simp [destinationObservations, observeDestination, Ne.symm different])
      _ valid.1
    intro phase matched
    cases phase <;> cases stage <;>
      simp_all [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress,
        runDestinationTrace, destinationObservations, observeDestination,
        runDestinationObservations, destinationTraceStep]
  · exact destinationCapabilities_replace state id _ (valid.2.1 id destination present) valid.2.1
  · apply destinationStorageReferences_replace state id _ storage
    · omega
    · simpa only [size, PendingDestination.storage, DestinationBacking.writeStorage] using
        (valid.2.2.1 id destination present).2
    · simpa only [size, DestinationBacking.receiverStorage] using
        (valid.2.2.1 id destination present).2
    · exact valid.2.2.1
  · exact destinationOwnersOrdered_replace state id destination _ present rfl valid.2.2.2

set_option maxHeartbeats 2000000 in
private theorem publicationStep_preserves (id : DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (publicationStep id state).finalState := by
  simp only [publicationStep, publishReady_transition, lookupDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination =>
      simp only [present]
      have inside := (Array.getElem?_eq_some_iff.mp present).choose
      cases progress : destination.progress <;> try simp only [progress] <;> try exact valid
      case built count =>
        cases use : destination.use <;> try simp only [use] <;> try exact valid
        case receiver =>
          cases backing : destination.backing with
          | direct receiver =>
              have receiverInside : receiver < state.storage.size := by
                simpa only [backing, DestinationBacking.receiverStorage] using
                  (valid.2.2.1 id destination present).2
              have committed := fun (start writeEnd : Nat) (storage : Array ReceivingStorage)
                  (size : storage.size = state.storage.size) =>
                publish_commit_lifecycle state id destination count start writeEnd none storage size
                  present progress valid
              simp only [backing, DestinationBacking.receiverStorage, use] at committed
              cases receiverResult : state.storage[receiver]?
              all_goals cases layout : destination.layout
              all_goals
                simp only [layout] at committed
                repeat' first
                  | simp only [backing, use, progress, layout, DestinationBacking.receiverStorage,
                      lookupStorage_result, receiverResult, replaceStorage_result, replaceDestination_result,
                      emit_result, receiverInside, inside, Array.size_set!, ↓reduceIte, bind, pure,
                      ConstructionM.fail, ConstructionResult.finalState, List.append_assoc]
                  | exact valid
                  | exact committed _ _ _ (by simp)
          | staged receiver stage =>
              have receiverInside : receiver < state.storage.size := by
                simpa only [backing, DestinationBacking.receiverStorage] using
                  (valid.2.2.1 id destination present).2
              have stageInside : stage < state.storage.size := by
                simpa only [PendingDestination.storage, backing, DestinationBacking.writeStorage] using
                  (valid.2.2.1 id destination present).1
              have committed := fun (start writeEnd : Nat) (storage : Array ReceivingStorage)
                  (size : storage.size = state.storage.size) =>
                publish_commit_lifecycle state id destination count start writeEnd (some stage) storage size
                  present progress valid
              simp only [backing, DestinationBacking.receiverStorage, use] at committed
              cases receiverResult : state.storage[receiver]?
              all_goals cases stageResult : state.storage[stage]?
              all_goals cases layout : destination.layout
              all_goals
                simp only [layout] at committed
                repeat' first
                  | simp only [backing, use, progress, layout, DestinationBacking.receiverStorage,
                      lookupStorage_result, receiverResult, stageResult, replaceStorage_result,
                      replaceDestination_result, emit_result, receiverInside, stageInside, inside,
                      Array.size_set!, ↓reduceIte, bind, pure, ConstructionM.fail,
                      ConstructionResult.finalState, List.append_assoc]
                  | exact valid
                  | exact committed _ _ _ (by simp)

private theorem publicationLoop_preserves (ids : List DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant
      (((do for id in ids do publicationStep id) : ConstructionM Unit) state).finalState := by
  induction ids generalizing state with
  | nil => exact valid
  | cons id ids ih =>
      have preserved := publicationStep_preserves id state valid
      cases result : publicationStep id state with
      | ok value after =>
          rw [result] at preserved
          simpa only [List.forIn_cons, bind, pure, result, ConstructionResult.finalState] using ih after preserved
      | fault kind after =>
          rw [result] at preserved
          simpa only [List.forIn_cons, bind, pure, result, ConstructionResult.finalState] using preserved

theorem publishOperation_destination_lifecycle_invariant (ids : List DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (publishOperation ids state).finalState := by
  simp only [publishOperation, ConstructionM.get, bind]
  cases checked : preflightPublication state ids with
  | error fault => exact valid
  | ok value =>
      cases value
      change DestinationLifecycleInvariant
        (((do for id in ids do publicationStep id) : ConstructionM Unit) state).finalState
      exact publicationLoop_preserves ids state valid

end Goose.Proofs.ConstructionExecutionProtocol
