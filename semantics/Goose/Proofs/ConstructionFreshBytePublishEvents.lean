import Goose.Proofs.ConstructionFreshByteBuildEvents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem carrierValue_completed_events (id : Nat) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState (carrierValue (.completed id) state)).construction.events = state.construction.events := by
  simp only [carrierValue, storedDestination, getDestination, EvalM.get, bind]
  cases found : state.construction.destinations[id]? with
  | none => simp [found, Goose.Construct.fault, EvalM.stop, Goose.Proofs.Exit.stepState]
  | some row =>
    cases progress : row.progress <;>
      simp [found, progress, progressCount, Goose.Construct.fault, EvalM.stop, pure, bind, Goose.Proofs.Exit.stepState]

theorem publishCompleted_direct_events (origin : Goose.Core.OriginId) (id count storageId : Nat)
    (state : ExecutionState) (row : PendingDestination) (present : state.construction.destinations[id]? = some row)
    (built : row.progress = .built count) (receiver : row.use = .receiver)
    (direct : row.backing = .direct storageId) (storage : ReceivingStorage)
    (stored : state.construction.storage[storageId]? = some storage) :
    ∃ suffix,
      (Goose.Proofs.Exit.stepState (publishCarriers origin [.completed id] state)).construction.events =
        state.construction.events ++ suffix ∧ ∀ event ∈ suffix, event = .publish id := by
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, _root_.id, liftConstruction]
  cases published : publishOperation [id] state.construction with
  | ok value after =>
    cases value
    have trace := byteOwner_publish_success_events state.construction after id count storageId row present built receiver direct storage stored published
    refine ⟨[.publish id], ?_, ?_⟩
    · simpa only [published, Goose.Proofs.Exit.stepState] using trace
    · simp
  | fault reason after =>
    have trace := byteOwner_publish_fault_events state.construction after id count storageId row present built receiver direct storage stored reason published
    refine ⟨[], ?_, by simp⟩
    cases reason <;> simpa only [published, Goose.Proofs.Exit.stepState, List.append_nil] using trace

#print axioms carrierValue_completed_events
#print axioms publishCompleted_direct_events

end Goose.Proofs.ConstructionAcceptedExecution
