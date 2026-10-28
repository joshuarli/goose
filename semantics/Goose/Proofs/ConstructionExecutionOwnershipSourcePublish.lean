import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataUpdates
import Goose.Proofs.ConstructionExecutionOwnershipSourceMutations

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

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

private theorem publish_commit_metadata (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (count start writeEnd : Nat) (stage : Option StorageId)
    (storage : Array ReceivingStorage) (size : storage.size = state.storage.size)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built count)
    (use : destination.use = .receiver) (valid : DestinationLifecycleInvariant state) :
    (ReservationMetadataFrame state { state with
      storage := storage
      destinations := state.destinations.set! id { destination with
        progress := .published count
        backing := .direct destination.backing.receiverStorage
        capability := { destination.capability with start := start }
        writeEnd := writeEnd }
      events := state.events ++ (match stage with
        | none => [.publish id]
        | some stage => [.copy (.storage stage []) id, .publish id]) }) ∧
    (OwnershipSourceExtension state { state with
      storage := storage
      destinations := state.destinations.set! id { destination with
        progress := .published count
        backing := .direct destination.backing.receiverStorage
        capability := { destination.capability with start := start }
        writeEnd := writeEnd }
      events := state.events ++ (match stage with
        | none => [.publish id]
        | some stage => [.copy (.storage stage []) id, .publish id]) }) := by
  constructor
  · apply reservationMetadataFrame_replace_mutable state id destination _ storage _ present
    · exact Nat.le_of_eq size.symm
    · simp [progress, ReservationStableProgress]
    · intro queried different
      cases stage <;> simp [destinationObservations, observeDestination, Ne.symm different]
  · refine ownershipSourceExtension_replace state id destination _ present ?_ ?_
    · rfl
    · simp [OwnershipLinkBacking, use, DestinationBacking.receiverStorage]

set_option maxHeartbeats 2000000 in
private theorem publicationStep_metadata (id : DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (publicationStep id state).finalState ∧
      OwnershipSourceExtension state (publicationStep id state).finalState := by
  simp only [publicationStep, publishReady_transition, lookupDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact ⟨.refl state, .refl state⟩
  | some destination =>
      simp only [present]
      have inside := (Array.getElem?_eq_some_iff.mp present).choose
      cases progress : destination.progress <;> try simp only [progress] <;> try exact ⟨.refl state, .refl state⟩
      case built count =>
        cases use : destination.use <;> try simp only [use] <;> try exact ⟨.refl state, .refl state⟩
        case receiver =>
          cases backing : destination.backing with
          | direct receiver =>
              have receiverInside : receiver < state.storage.size := by
                simpa only [backing, DestinationBacking.receiverStorage] using
                  (valid.2.2.1 id destination present).2
              have committed := fun (start writeEnd : Nat) (storage : Array ReceivingStorage)
                  (size : storage.size = state.storage.size) =>
                publish_commit_metadata state id destination count start writeEnd none storage size
                  present progress use valid
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
                  | exact ⟨.refl state, .refl state⟩
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
                publish_commit_metadata state id destination count start writeEnd (some stage) storage size
                  present progress use valid
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
                  | exact ⟨.refl state, .refl state⟩
                  | exact committed _ _ _ (by simp)

private theorem publicationLoop_preserves (ids : List DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant
      (((do for id in ids do publicationStep id) : ConstructionM Unit) state).finalState ∧
      ReservationMetadataFrame state (((do for id in ids do publicationStep id) : ConstructionM Unit) state).finalState ∧
      OwnershipSourceExtension state (((do for id in ids do publicationStep id) : ConstructionM Unit) state).finalState := by
  induction ids generalizing state with
  | nil => exact ⟨valid, .refl state, .refl state⟩
  | cons id ids ih =>
      have preserved := And.intro (publicationStep_preserves id state valid) (publicationStep_metadata id state valid)
      cases result : publicationStep id state with
      | ok value after =>
          rw [result] at preserved
          have remaining := ih after preserved.1
          simpa only [List.forIn_cons, bind, pure, result, ConstructionResult.finalState] using
            And.intro remaining.1 (And.intro (preserved.2.1.trans remaining.2.1)
              (ownershipSourceExtension_trans _ _ _ preserved.2.2 remaining.2.2))
      | fault kind after =>
          rw [result] at preserved
          simpa only [List.forIn_cons, bind, pure, result, ConstructionResult.finalState] using preserved

theorem publishOperation_ownership_source (ids : List DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    OwnershipSourceExtension state (publishOperation ids state).finalState := by
  simp only [publishOperation, ConstructionM.get, bind]
  cases checked : preflightPublication state ids with
  | error fault => exact .refl state
  | ok value =>
      cases value
      change OwnershipSourceExtension state
        (((do for id in ids do publicationStep id) : ConstructionM Unit) state).finalState
      exact (publicationLoop_preserves ids state valid).2.2

end Goose.Proofs.ConstructionExecutionOwnership
