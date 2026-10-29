import Goose.Proofs.ConstructionExitWrittenCancelWorld
import Goose.Proofs.ConstructionExitDirectResumption

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem protected_direct_cancel_equivalent (state : ExecutionState) (origin : OriginId)
    (token incoming selected count : Nat) (snapshot row : PendingDestination) (storage : ReceivingStorage)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (present : state.construction.destinations[selected]? = some row) (identity : row.capability.id = selected)
    (phase : row.progress = .open count ∨ row.progress = .built count)
    (writable : destinationCanWrite state.construction selected = true)
    (stored : state.construction.storage[row.storage]? = some storage)
    (current : destinationCurrent state.construction selected = .ok selected)
    (leaf : treeRows state.construction selected = [row]) (direct : selected = snapshot.capability.id) :
    let cleaned := abandonRowState state.construction selected row storage
    cleanupReceivingDestination origin selected [] state = .ok () { state with construction := cleaned } ∧
    cancelExitReservation token [] cleaned = cancelExitReservation token [] state.construction := by
  let cleaned := abandonRowState state.construction selected row storage
  have tree : abandonTree selected state.construction = .ok () cleaned :=
    abandon_leaf_success state.construction selected count row storage present identity phase writable stored leaf
  have active : activeRow row = true := by rcases phase with phase | phase <;> simp [activeRow, phase]
  have progress : activeProgress row.progress = true := by rcases phase with phase | phase <;> simp [activeProgress, phase]
  have cleanedFound : cleaned.destinations[selected]? = some { row with progress := .abandoned } := by
    simp only [cleaned, abandonRowState, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp present).1
  have cleanedCurrent : destinationCurrent cleaned selected = .ok selected := by
    rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ state.construction cleaned (by simp [cleaned, abandonRowState]) rfl,
      show cleaned.destinations.size = state.construction.destinations.size by simp [cleaned, abandonRowState]]
    simpa only [destinationCurrent_result] using current
  have cleanedTicket : cleaned.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := ticket
  have activeCancel := cancel_active_direct_saves_snapshot state.construction cleaned token incoming selected selected snapshot row
    ticket current present active tree direct
  have inactiveCancel := cancel_inactive_direct_saves_snapshot cleaned token incoming selected selected snapshot
    { row with progress := .abandoned } cleanedTicket cleanedCurrent cleanedFound (by simp [activeRow]) direct
  refine ⟨?_, inactiveCancel.trans activeCancel.symm⟩
  simp only [cleanupReceivingDestination, receivingDestination, liftConstruction, current, bind, pure,
    cleanupDestination, getDestination, EvalM.get, present, progress, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, protectedReplacement?, List.findSome?_nil, List.any_nil, tree]
  rfl

#print axioms protected_direct_cancel_equivalent

end Goose.Proofs.ConstructionAcceptedExecution
