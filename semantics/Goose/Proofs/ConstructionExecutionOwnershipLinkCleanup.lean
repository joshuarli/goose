import Goose.Proofs.ConstructionExecutionOwnershipLinks
import Goose.Proofs.ConstructionExecutionOwnershipTree
import Goose.Proofs.ConstructionExecutionOwnershipLinkMutations

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem treeAbandonRowState_preserves_forwardLinks (state : ConstructionState)
    (row : PendingDestination) (present : state.destinations[row.capability.id]? = some row)
    (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (treeAbandonRowState state row) := by
  exact destinationForwardLinks_replace state row.capability.id row
    { row with progress := .abandoned } present rfl rfl valid (by simp [DestinationForwardLink])

theorem treeAbandonRowsState_preserves_forwardLinks (rows : List PendingDestination)
    (state : ConstructionState)
    (current : ∀ row ∈ rows, state.destinations[row.capability.id]? = some row)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id)
    (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (treeAbandonRowsState rows state) := by
  induction rows generalizing state with
  | nil => exact valid
  | cons row rest ih =>
      apply ih (treeAbandonRowState state row)
      · intro next member
        have different := (List.pairwise_cons.mp unique).1 next member
        simpa only [treeAbandonRowState, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne different] using current next (List.mem_cons_of_mem _ member)
      · exact (List.pairwise_cons.mp unique).2
      · exact treeAbandonRowState_preserves_forwardLinks state row
          (current row (List.mem_cons_self ..)) valid

theorem treeCleanupStep_forwardLinks (row : PendingDestination) (state : ConstructionState)
    (present : state.destinations[row.capability.id]? = some row)
    (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (treeCleanupStep row state).finalState := by
  rw [treeCleanupStep_current_equation row state present]
  cases writable : destinationCanWrite state row.capability.id with
  | false => exact valid
  | true =>
      simp only [↓reduceIte]
      cases progress : row.progress <;>
        try exact abandonDestination_forwardLinks state row.capability.id valid
      case suspended count child =>
        exact abandonDestination_forwardLinks _ row.capability.id
          (destinationForwardLinks_replace_leaf state row.capability.id row
            { row with progress := .open count } present rfl rfl (by trivial) valid)

theorem treeCleanupLoop_forwardLinks (rows : List PendingDestination) (state : ConstructionState)
    (current : ∀ row ∈ rows, state.destinations[row.capability.id]? = some row)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id)
    (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (treeCleanupLoop rows state).finalState := by
  induction rows generalizing state with
  | nil => exact valid
  | cons row rest ih =>
      simp only [treeCleanupLoop, bind]
      have first := treeCleanupStep_forwardLinks row state (current row (List.mem_cons_self ..)) valid
      cases result : treeCleanupStep row state with
      | fault kind after => simpa only [result, ConstructionResult.finalState] using first
      | ok value after =>
          cases value
          have exactState := treeCleanupStep_success state after row
            (current row (List.mem_cons_self ..)) result
          simp only [result, ConstructionResult.finalState] at first
          subst after
          apply ih (treeAbandonRowState state row)
          · intro next member
            have different := (List.pairwise_cons.mp unique).1 next member
            simpa only [treeAbandonRowState, Array.set!_eq_setIfInBounds,
              Array.getElem?_setIfInBounds_ne different] using current next (List.mem_cons_of_mem _ member)
          · exact (List.pairwise_cons.mp unique).2
          · exact first

theorem abandonTree_forwardLinks_all_outcomes (state : ConstructionState) (id : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state) (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (abandonTree id state).finalState := by
  rw [abandonTree_cleanup_equation]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some parent =>
      cases writable : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [↓reduceIte]
          cases progress : parent.progress <;> simp only [progress] <;> try exact valid
          all_goals
            by_cases exiting : treeHasExiting (treeRows state id) = true
            · simpa only [exiting, Bool.false_eq_true, ↓reduceIte, ConstructionResult.finalState] using valid
            · simpa only [exiting, Bool.false_eq_true, ↓reduceIte] using treeCleanupLoop_forwardLinks (treeRows state id) state
                (treeRows_indexed state id indexed).1 (treeRows_indexed state id indexed).2 valid

end Goose.Proofs.ConstructionExecutionOwnership
