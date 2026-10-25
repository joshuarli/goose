import Goose.Proofs.ConstructionExecutionOwnershipSourceMutations
import Goose.Proofs.ConstructionExecutionOwnershipLinkCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem abandonRowsState_ownership_source (rows : List PendingDestination) (state : ConstructionState)
    (current : ∀ row ∈ rows, state.destinations[row.capability.id]? = some row)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id) :
    OwnershipSourceExtension state (abandonRowsState rows state) := by
  induction rows generalizing state with
  | nil => exact .refl state
  | cons row rest ih =>
      let next : ConstructionState := { state with
        destinations := state.destinations.set! row.capability.id { row with progress := .abandoned }
        events := state.events ++ [.abandon row.capability.id] }
      have present := current row (List.mem_cons_self ..)
      have first : OwnershipSourceExtension state next :=
        ownershipSourceExtension_replace state row.capability.id row _ present rfl
          (by cases use : row.use <;> simp [OwnershipLinkBacking, use])
      have remaining := ih next (by
        intro after member
        have different := (List.pairwise_cons.mp unique).1 after member
        simpa only [next, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different]
          using current after (List.mem_cons_of_mem _ member)) (List.pairwise_cons.mp unique).2
      simpa only [abandonRowsState, next] using ownershipSourceExtension_trans state next _ first remaining

theorem abandonPreservingExit_ownership_source (id replacement : DestinationId) (state : ConstructionState)
    (indexed : DestinationCapabilitiesIndexed state) :
    OwnershipSourceExtension state (abandonPreservingExit id replacement state).finalState := by
  cases checked : protectedExitDiscarded state id replacement with
  | error fault =>
      simp only [abandonPreservingExit, ConstructionM.get, bind, checked, ConstructionM.fail,
        ConstructionResult.finalState]
      exact .refl state
  | ok rows =>
      rw [abandonPreservingExit_exact state id replacement indexed ⟨rows, checked⟩]
      apply abandonRowsState_ownership_source (protectedRows state id replacement) state ?_
        (protectedRows_indexed state id replacement indexed).2
      intro row member
      have original := (protectedRows_exact_selection state id replacement row).mp member
      obtain ⟨index, found⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp original.1)
      simpa only [indexed index row found] using found

private theorem treeCleanupStep_ownership_source (row : PendingDestination) (state : ConstructionState)
    (present : state.destinations[row.capability.id]? = some row) :
    OwnershipSourceExtension state (treeCleanupStep row state).finalState := by
  rw [treeCleanupStep_current_equation row state present]
  cases writable : destinationCanWrite state row.capability.id with
  | false => exact .refl state
  | true =>
      simp only [↓reduceIte]
      cases progress : row.progress <;>
        try exact abandonDestination_ownership_source state row.capability.id
      case suspended count child =>
        exact ownershipSourceExtension_trans _ _ _
          (ownershipSourceExtension_replace state row.capability.id row
            { row with progress := .open count } present rfl
            (by cases use : row.use <;> simp [OwnershipLinkBacking, use]))
          (abandonDestination_ownership_source _ row.capability.id)

private theorem treeCleanupLoop_ownership_source (rows : List PendingDestination) (state : ConstructionState)
    (current : ∀ row ∈ rows, state.destinations[row.capability.id]? = some row)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id) :
    OwnershipSourceExtension state (treeCleanupLoop rows state).finalState := by
  induction rows generalizing state with
  | nil => exact .refl state
  | cons row rest ih =>
      simp only [treeCleanupLoop, bind]
      have first := treeCleanupStep_ownership_source row state (current row (List.mem_cons_self ..))
      cases result : treeCleanupStep row state with
      | fault kind after => simpa only [result, ConstructionResult.finalState] using first
      | ok value after =>
          cases value
          have exactState := treeCleanupStep_success state after row
            (current row (List.mem_cons_self ..)) result
          simp only [result, ConstructionResult.finalState] at first
          subst after
          have remaining := ih (treeAbandonRowState state row) (by
            intro next member
            have different := (List.pairwise_cons.mp unique).1 next member
            simpa only [treeAbandonRowState, Array.set!_eq_setIfInBounds,
              Array.getElem?_setIfInBounds_ne different] using current next (List.mem_cons_of_mem _ member))
            (List.pairwise_cons.mp unique).2
          exact ownershipSourceExtension_trans _ _ _ first remaining

theorem abandonTree_ownership_source (id : DestinationId) (state : ConstructionState)
    (indexed : DestinationCapabilitiesIndexed state) :
    OwnershipSourceExtension state (abandonTree id state).finalState := by
  rw [abandonTree_cleanup_equation]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some parent =>
      cases writable : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [↓reduceIte]
          cases progress : parent.progress <;> simp only [progress] <;> try exact .refl state
          all_goals
            by_cases exiting : treeHasExiting (treeRows state id) = true
            · simpa only [exiting, Bool.false_eq_true, ↓reduceIte, ConstructionResult.finalState] using OwnershipSourceExtension.refl state
            · simpa only [exiting, Bool.false_eq_true, ↓reduceIte] using treeCleanupLoop_ownership_source (treeRows state id) state
                (treeRows_indexed state id indexed).1 (treeRows_indexed state id indexed).2

end Goose.Proofs.ConstructionExecutionOwnership
