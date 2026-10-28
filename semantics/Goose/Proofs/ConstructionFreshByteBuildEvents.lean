import Goose.Proofs.ConstructionFreshByteCompletionEvents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ConstructionExecutionOwnership

theorem buildExpr_byteOwner_fresh_events (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (before state : ExecutionState)
    (frame : FreshDestinationFrame before state) (storageId count : Nat)
    (direct : frame.row.backing = .direct storageId) (fresh : storageId = before.construction.storage.size)
    (opened : frame.row.progress = .open count) (valid : DestinationLifecycleInvariant state.construction)
    (current : destinationCurrent state.construction before.construction.destinations.size =
      .ok before.construction.destinations.size) :
    ∃ suffix,
      (Goose.Proofs.Exit.stepState (buildExpr (fuel + 1) config environment before.construction.destinations.size
        (.bytes (.varr (.int .u8)) bytes origin) state)).construction.events = state.construction.events ++ suffix ∧
      ∀ event ∈ suffix, ∃ index, event = .write before.construction.destinations.size index := by
  let id := before.construction.destinations.size
  change destinationCurrent state.construction id = .ok id at current
  have present : state.construction.destinations[id]? = some frame.row := by
    rw [frame.destinations]
    exact Array.getElem?_push_size
  have renewal : renewReceivingDestination id state.construction = .ok id state.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure, lookupDestination_result, present, opened]
  let loop : EvalM PUnit := forIn bytes PUnit.unit fun byte _ => do
    receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
    pure (.yield PUnit.unit)
  obtain ⟨suffix, trace, onlyWrites⟩ := bytes_writeLoop_fresh_events bytes origin before state frame storageId count
    direct fresh opened current
  change (Goose.Proofs.Exit.stepState (loop state)).construction.events = _ at trace
  refine ⟨suffix, ?_, onlyWrites⟩
  change (Goose.Proofs.Exit.stepState (buildExpr (fuel + 1) config environment id
    (.bytes (.varr (.int .u8)) bytes origin) state)).construction.events = _
  simp only [buildExpr, expressionOrigin, liftConstruction, renewal, bind]
  change (Goose.Proofs.Exit.stepState (protectDestination origin id
    (loop >>= fun _ => receivingAction origin id finishDestination) state)).construction.events = _
  cases ran : loop state with
  | stop reason middle =>
    simp only [ran, Goose.Proofs.Exit.stepState] at trace
    simpa only [protectDestination, bind, ran, Goose.Proofs.Exit.stepState] using trace
  | escape target carriers middle =>
    have localAction : LocalConstructionAction loop := bytes_writeLoop_local bytes origin id
    have impossible := localAction state
    rw [ran] at impossible
    cases impossible
  | jump target kind middle =>
    have localAction : LocalConstructionAction loop := bytes_writeLoop_local bytes origin id
    have impossible := localAction state
    rw [ran] at impossible
    cases impossible
  | ok value middle =>
    cases value
    have ran' := ran
    simp only [loop, bind] at ran'
    obtain ⟨_, _, current', row, n, rowPresent, rowOpened⟩ :=
      bytes_writeLoop_ownershipSource bytes origin id state middle frame.row count valid current present opened ran'
    have finishedTrace := byteOwner_finish_events origin id n middle row current' rowPresent rowOpened
    simp only [ran, Goose.Proofs.Exit.stepState] at trace
    cases finished : receivingAction origin id finishDestination middle with
    | ok value after =>
      cases value
      simp only [finished, Goose.Proofs.Exit.stepState] at finishedTrace
      simp only [protectDestination, bind, ran, finished, Goose.Proofs.Exit.stepState]
      exact finishedTrace.trans trace
    | stop reason after =>
      simp only [finished, Goose.Proofs.Exit.stepState] at finishedTrace
      simp only [protectDestination, bind, ran, finished, Goose.Proofs.Exit.stepState]
      exact finishedTrace.trans trace
    | escape target carriers after =>
      have localAction : LocalConstructionAction (receivingAction origin id finishDestination) := LocalConstructionAction.lift origin _
      have impossible := localAction middle
      rw [finished] at impossible
      cases impossible
    | jump target kind after =>
      have localAction : LocalConstructionAction (receivingAction origin id finishDestination) := LocalConstructionAction.lift origin _
      have impossible := localAction middle
      rw [finished] at impossible
      cases impossible

#print axioms buildExpr_byteOwner_fresh_events

end Goose.Proofs.ConstructionAcceptedExecution
