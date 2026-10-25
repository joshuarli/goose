import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsForwardFrame
import Goose.Proofs.ConstructionExecutionOwnershipLinkCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

private def TreeOwnershipRows (before after : ConstructionState) : Prop :=
  OwnershipChildSourceExtension before after ∧
    (∀ (id : DestinationId) (row : PendingDestination), before.destinations[id]? = some row →
      ∀ count selected, row.progress = .exiting count selected → after.destinations[id]? = some row) ∧
    (SupportedReplacementAuthorityRows before.destinations → SupportedReplacementAuthorityRows after.destinations)

private theorem TreeOwnershipRows.refl (state : ConstructionState) : TreeOwnershipRows state state :=
  ⟨ownershipChildSourceExtension_refl state, (fun _ _ present _ _ _ => present), id⟩

private theorem TreeOwnershipRows.trans {before middle after : ConstructionState}
    (first : TreeOwnershipRows before middle) (second : TreeOwnershipRows middle after) :
    TreeOwnershipRows before after :=
  ⟨ownershipChildSourceExtension_trans before middle after first.1 second.1,
    fun id row present count selected exiting =>
      second.2.1 id row (first.2.1 id row present count selected exiting) count selected exiting,
    fun valid => second.2.2 (first.2.2 valid)⟩

private theorem treeOwnershipRows_weaken {before after : ConstructionState}
    (frame : TreeOwnershipRows before after) : OwnershipLinkRowsFrame before after := by
  refine ⟨frame.1, ?_, frame.2.2⟩
  intro id initial final initialPresent finalPresent count selected initialExiting _ _ _
  exact Option.some.inj (finalPresent.symm.trans (frame.2.1 id initial initialPresent count selected initialExiting))

private theorem treeOwnershipRows_replace_mutable (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (mutable : ¬ ReservationStableProgress before.progress) :
    TreeOwnershipRows state { state with destinations := state.destinations.set! id after } := by
  have frame := ownershipLinkRowsFrame_replace_mutable state id before after present sameUse backing mutable
  refine ⟨frame.children, ?_, frame.2.2⟩
  intro index row found count selected exiting
  have different : id ≠ index := by
    intro same
    subst index
    have equal := Option.some.inj (present.symm.trans found)
    subst row
    exact mutable (by simp [ReservationStableProgress, exiting])
  simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different] using found

private theorem abandonDestination_treeOwnershipRows (state : ConstructionState) (id : DestinationId) :
    TreeOwnershipRows state (abandonDestination id state).finalState := by
  simp only [abandonDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact .refl state
          all_goals
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[row.storage]? with
            | none => exact .refl state
            | some storage =>
                have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
                simp only [stored, replaceStorage_result, replaceDestination_result,
                  storageInside, inside, ↓reduceIte, bind, pure, emit_result, ConstructionResult.finalState]
                refine treeOwnershipRows_replace_mutable state id row _ present ?_ ?_ ?_
                · rfl
                · cases use : row.use <;> simp [OwnershipLinkBacking, use]
                · simp [ReservationStableProgress, progress]

private theorem treeCleanupStep_ownershipRows (row : PendingDestination) (state : ConstructionState)
    (present : state.destinations[row.capability.id]? = some row) :
    TreeOwnershipRows state (treeCleanupStep row state).finalState := by
  rw [treeCleanupStep_current_equation row state present]
  cases writable : destinationCanWrite state row.capability.id with
  | false => exact .refl state
  | true =>
      simp only [↓reduceIte]
      cases progress : row.progress <;>
        try exact abandonDestination_treeOwnershipRows state row.capability.id
      case suspended count child =>
        exact TreeOwnershipRows.trans
          (treeOwnershipRows_replace_mutable state row.capability.id row
            { row with progress := .open count } present rfl
            (by cases use : row.use <;> simp [OwnershipLinkBacking, use])
            (by simp [ReservationStableProgress, progress]))
          (abandonDestination_treeOwnershipRows _ row.capability.id)

private theorem treeCleanupLoop_ownershipRows (rows : List PendingDestination) (state : ConstructionState)
    (current : ∀ row ∈ rows, state.destinations[row.capability.id]? = some row)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id) :
    TreeOwnershipRows state (treeCleanupLoop rows state).finalState := by
  induction rows generalizing state with
  | nil => exact .refl state
  | cons row rest ih =>
      simp only [treeCleanupLoop, bind]
      have first := treeCleanupStep_ownershipRows row state (current row (List.mem_cons_self ..))
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
          exact TreeOwnershipRows.trans first remaining

theorem abandonTree_ownership_frame (id : DestinationId) (state : ConstructionState)
    (indexed : DestinationCapabilitiesIndexed state) :
    OwnershipForwardRowsFrame state (abandonTree id state).finalState := by
  constructor
  · apply treeOwnershipRows_weaken
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
              · simpa only [exiting, Bool.false_eq_true, ↓reduceIte, ConstructionResult.finalState] using TreeOwnershipRows.refl state
              · simpa only [exiting, Bool.false_eq_true, ↓reduceIte] using treeCleanupLoop_ownershipRows (treeRows state id) state
                  (treeRows_indexed state id indexed).1 (treeRows_indexed state id indexed).2
  · exact abandonTree_forwardLinks_all_outcomes state id indexed

end Goose.Proofs.ConstructionExecutionOwnership
