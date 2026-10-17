import Goose.Proofs.ExitExecutionCleanupStoragePrefixes

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core

theorem StoragePrefixesEqual.lookup (limit : StorageId → Nat)
    (before after : Array ReceivingStorage) (framed : StoragePrefixesEqual limit before after)
    (id : StorageId) (previous : ReceivingStorage) (present : before[id]? = some previous) :
    ∃ current, after[id]? = some current ∧ current.publishedCount = previous.publishedCount ∧
      current.bytes.extract 0 (limit id) = previous.bytes.extract 0 (limit id) := by
  have observed := framed id
  cases found : after[id]? with
  | none => simp [storagePrefixObservation, found, present] at observed
  | some current =>
      have same : (current.publishedCount, current.bytes.extract 0 (limit id)) =
          (previous.publishedCount, previous.bytes.extract 0 (limit id)) := by
        simpa only [storagePrefixObservation, found, present, Option.map_some, Option.some.injEq]
          using observed
      exact ⟨current, rfl, congrArg Prod.fst same, congrArg Prod.snd same⟩

theorem getStorage_prefix_observation (limit : StorageId → Nat) (id : StorageId)
    (before after : ExecutionState)
    (framed : StoragePrefixesEqual limit before.construction.storage after.construction.storage) :
    mapStepState (fun _ => ExecutionState.initial)
      ((do let entry ← getStorage id
           pure (entry.publishedCount, entry.bytes.extract 0 (limit id))) after) =
    mapStepState (fun _ => ExecutionState.initial)
      ((do let entry ← getStorage id
           pure (entry.publishedCount, entry.bytes.extract 0 (limit id))) before) := by
  cases present : before.construction.storage[id]? with
  | none =>
      have missing : after.construction.storage[id]? = none := by
        have observed := framed id
        cases found : after.construction.storage[id]? with
        | none => rfl
        | some entry => simp [storagePrefixObservation, found, present] at observed
      simp only [getStorage, EvalM.get, bind, missing, present, Goose.Construct.fault, EvalM.stop, mapStepState]
  | some previous =>
      obtain ⟨current, found, count, bytes⟩ := framed.lookup _ _ _ id previous present
      simp only [getStorage, EvalM.get, bind, pure, found, present, mapStepState, count, bytes]

def StoredSamplingMetadataEqual (stored : StoredValue) (before after : ExecutionState) : Prop :=
  ∀ id, stored.destination = some id →
    after.construction.destinations[id]? = before.construction.destinations[id]?

theorem sampledStored_prefix_observation (limit : StorageId → Nat) (stored : StoredValue)
    (before after : ExecutionState)
    (framed : StoragePrefixesEqual limit before.construction.storage after.construction.storage)
    (metadata : StoredSamplingMetadataEqual stored before after) :
    mapStepState (fun _ => ExecutionState.initial)
      ((do let (bytes, run) ← sampledStored stored
           pure (bytes.extract 0 (limit stored.storage), run)) after) =
    mapStepState (fun _ => ExecutionState.initial)
      ((do let (bytes, run) ← sampledStored stored
           pure (bytes.extract 0 (limit stored.storage), run)) before) := by
  cases present : before.construction.storage[stored.storage]? with
  | none =>
      have missing : after.construction.storage[stored.storage]? = none := by
        have observed := framed stored.storage
        cases found : after.construction.storage[stored.storage]? with
        | none => rfl
        | some entry => simp [storagePrefixObservation, found, present] at observed
      simp only [sampledStored, getStorage, EvalM.get, bind, missing, present, Goose.Construct.fault,
        EvalM.stop, mapStepState]
  | some previous =>
      obtain ⟨current, found, count, bytes⟩ := framed.lookup _ _ _ stored.storage previous present
      cases destination : stored.destination with
      | none =>
          cases element : elementType stored.ty <;>
            simp only [sampledStored, getStorage, EvalM.get, bind, pure, found, present,
              destination, element, Goose.Construct.fault, EvalM.stop, mapStepState, bytes]
      | some id =>
          have destinationFrame := metadata id destination
          cases selected : before.construction.destinations[id]? with
          | none =>
              simp only [sampledStored, getStorage, getDestination, EvalM.get, bind, pure,
                found, present, destination, destinationFrame, selected, Goose.Construct.fault, EvalM.stop,
                mapStepState]
          | some pending =>
              cases progress : pending.progress <;>
                cases element : elementType stored.ty <;>
                simp only [sampledStored, getStorage, getDestination, EvalM.get, bind, pure,
                  found, present, destination, destinationFrame, selected, progress, element,
                  progressCount, Goose.Construct.fault, EvalM.stop, mapStepState, bytes, count]

end Goose.Proofs.ExitExecution
