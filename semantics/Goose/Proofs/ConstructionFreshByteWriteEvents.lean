import Goose.Proofs.ConstructionByteWriteStopped

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionStorage

theorem bytes_writeLoop_fresh_events (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before state : ExecutionState) (frame : FreshDestinationFrame before state) (storageId count : Nat)
    (direct : frame.row.backing = .direct storageId) (fresh : storageId = before.construction.storage.size)
    (opened : frame.row.progress = .open count)
    (current : destinationCurrent state.construction before.construction.destinations.size =
      .ok before.construction.destinations.size) :
    ∃ suffix,
      (Goose.Proofs.Exit.stepState (((forIn bytes PUnit.unit fun byte _ => do
        receivingAction origin before.construction.destinations.size (fun destination => writeElement destination ⟨#[byte]⟩)
        pure (.yield PUnit.unit)) : EvalM PUnit) state)).construction.events = state.construction.events ++ suffix ∧
      ∀ event ∈ suffix, ∃ index, event = .write before.construction.destinations.size index := by
  induction bytes generalizing state count with
  | nil =>
    refine ⟨[], ?_, by simp⟩
    simp [List.forIn_nil, pure, Goose.Proofs.Exit.stepState]
  | cons byte rest ih =>
    have present : state.construction.destinations[before.construction.destinations.size]? = some frame.row := by
      rw [frame.destinations]
      exact Array.getElem?_push_size
    have renewal : renewReceivingDestination before.construction.destinations.size state.construction =
        .ok before.construction.destinations.size state.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
        lookupDestination_result, present, opened]
    have events := writeElement_write_events before.construction.destinations.size ⟨#[byte]⟩ state.construction
    cases written : writeElement before.construction.destinations.size ⟨#[byte]⟩ state.construction with
    | fault reason final =>
      have transition := writeElement_transition before.construction.destinations.size ⟨#[byte]⟩ state.construction
      rw [written] at transition
      cases transition
      refine ⟨[], ?_, by simp⟩
      cases reason <;> simp [List.forIn_cons, receivingAction, liftConstruction, renewal, bind, written,
        Goose.Proofs.Exit.stepState, pure]
    | ok value final =>
      cases value
      obtain ⟨next, nextDirect⟩ := frame.writeElement ⟨#[byte]⟩ final storageId direct fresh written
      have row' := writeElement_success_destination before.construction.destinations.size ⟨#[byte]⟩
        state.construction final frame.row count present opened written
      have nextPresent : final.destinations[before.construction.destinations.size]? = some next.row := by
        rw [next.destinations]
        exact Array.getElem?_push_size
      have same := Option.some.inj (nextPresent.symm.trans row'.1)
      have nextOpened : next.row.progress = .open (count + 1) := by rw [same]
      have indexing := writeElement_preserves_indexing before.construction.destinations.size ⟨#[byte]⟩ state.construction
      rw [written] at indexing
      simp only [ConstructionResult.finalState] at indexing
      have current' : destinationCurrent final before.construction.destinations.size =
          .ok before.construction.destinations.size := by
        rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ state.construction final indexing.1 indexing.2, indexing.1]
        simpa only [destinationCurrent_result] using current
      obtain ⟨suffix, equal, onlyWrites⟩ := ih { state with construction := final } next (count + 1) nextDirect nextOpened current'
      obtain ⟨first, firstEqual, firstWrites⟩ := events
      simp only [written, ConstructionResult.finalState] at firstEqual
      refine ⟨first ++ suffix, ?_, ?_⟩
      · simp only [List.forIn_cons, receivingAction, liftConstruction, renewal, bind, written, pure]
        simpa only [firstEqual, List.append_assoc, receivingAction, liftConstruction, bind, pure] using equal
      · intro event member
        simp only [List.mem_append] at member
        rcases member with member | member
        · exact firstWrites event member
        · exact onlyWrites event member

#print axioms bytes_writeLoop_fresh_events

end Goose.Proofs.ConstructionAcceptedExecution
