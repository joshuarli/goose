import Goose.Proofs.ConstructionFreshByteAllocationEvents
import Goose.Proofs.ConstructionBytePublishStopped

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem byteOwner_finish_events (origin : Goose.Core.OriginId) (id count : Nat) (state : ExecutionState)
    (row : PendingDestination) (current : destinationCurrent state.construction id = .ok id)
    (present : state.construction.destinations[id]? = some row) (opened : row.progress = .open count) :
    (Goose.Proofs.Exit.stepState (receivingAction origin id finishDestination state)).construction.events =
      state.construction.events := by
  have renewal : renewReceivingDestination id state.construction = .ok id state.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure, lookupDestination_result, present, opened]
  have kept := finishDestination_events_unchanged id state.construction
  simp only [receivingAction, liftConstruction, renewal, bind]
  cases finished : finishDestination id state.construction with
  | ok value after =>
    cases value
    simp only [finished, ConstructionResult.finalState] at kept
    simpa only [finished, Goose.Proofs.Exit.stepState] using kept
  | fault reason after =>
    simp only [finished, ConstructionResult.finalState] at kept
    cases reason <;> simpa only [finished, Goose.Proofs.Exit.stepState] using kept

theorem byteOwner_publish_success_events (state after : ConstructionState) (id count storageId : Nat)
    (row : PendingDestination) (present : state.destinations[id]? = some row)
    (built : row.progress = .built count) (receiver : row.use = .receiver)
    (direct : row.backing = .direct storageId) (storage : ReceivingStorage)
    (stored : state.storage[storageId]? = some storage)
    (executed : publishOperation [id] state = .ok () after) :
    after.events = state.events ++ [.publish id] := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [publishOperation, ConstructionM.get, bind] at executed
  cases check : preflightPublication state [id] with
  | error fault => simp only [check, ConstructionM.fail, reduceCtorEq] at executed
  | ok value =>
    cases value
    simp only [check, List.forIn_cons, List.forIn_nil, publishReady_transition,
      lookupDestination_result, present, bind, built, receiver, direct, DestinationBacking.receiverStorage,
      lookupStorage_result, stored, replaceStorage_result, replaceDestination_result, storageInside, inside,
      ↓reduceIte, emit_result, pure, ConstructionResult.ok.injEq] at executed
    obtain ⟨same⟩ := executed
    subst after
    rfl

theorem byteOwner_publish_fault_events (state after : ConstructionState) (id count storageId : Nat)
    (row : PendingDestination) (present : state.destinations[id]? = some row)
    (built : row.progress = .built count) (receiver : row.use = .receiver)
    (direct : row.backing = .direct storageId) (storage : ReceivingStorage)
    (stored : state.storage[storageId]? = some storage) (reason : ConstructionFault)
    (executed : publishOperation [id] state = .fault reason after) : after.events = state.events := by
  rw [publishPacked_fault_unchanged state after id count storageId row present built receiver direct storage stored reason executed]

#print axioms byteOwner_finish_events
#print axioms byteOwner_publish_success_events
#print axioms byteOwner_publish_fault_events

end Goose.Proofs.ConstructionAcceptedExecution
