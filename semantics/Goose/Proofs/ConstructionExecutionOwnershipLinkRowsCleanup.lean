import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsForwardFrame
import Goose.Proofs.ConstructionExecutionOwnershipCleanup
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataUpdates

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem abandonRowsState_ownership_frame (rows : List PendingDestination) (state : ConstructionState)
    (current : ∀ row ∈ rows, state.destinations[row.capability.id]? = some row)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id) :
    ReservationMetadataFrame state (abandonRowsState rows state) ∧
      OwnershipForwardRowsFrame state (abandonRowsState rows state) := by
  induction rows generalizing state with
  | nil => exact ⟨.refl state, .refl state⟩
  | cons row rest ih =>
      let next : ConstructionState := { state with
        destinations := state.destinations.set! row.capability.id { row with progress := .abandoned }
        events := state.events ++ [.abandon row.capability.id] }
      have present := current row (List.mem_cons_self ..)
      have firstMetadata : ReservationMetadataFrame state next := by
        apply reservationMetadataFrame_replace_terminal state row.capability.id row _ state.storage _ present (Nat.le_refl _)
        · trivial
        · intro count selected; simp
        · intro index different
          simp [destinationObservations, observeDestination, Ne.symm different]
      have first : OwnershipForwardRowsFrame state next := by
        refine ownershipForwardRowsFrame_replace_terminal state row.capability.id row _ present rfl ?_ ?_ rfl (Or.inr (Or.inl rfl))
        · cases use : row.use <;> simp [OwnershipLinkBacking, use]
        · trivial
      have remaining := ih next (by
        intro after member
        have different := (List.pairwise_cons.mp unique).1 after member
        simpa only [next, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different]
          using current after (List.mem_cons_of_mem _ member)) (List.pairwise_cons.mp unique).2
      simpa only [abandonRowsState, next] using And.intro (firstMetadata.trans remaining.1)
        (OwnershipForwardRowsFrame.trans firstMetadata remaining.1 first remaining.2)

theorem abandonPreservingExit_ownership_frame (id replacement : DestinationId) (state : ConstructionState)
    (indexed : DestinationCapabilitiesIndexed state) :
    OwnershipForwardRowsFrame state (abandonPreservingExit id replacement state).finalState := by
  cases checked : protectedExitDiscarded state id replacement with
  | error fault =>
      simp only [abandonPreservingExit, ConstructionM.get, bind, checked, ConstructionM.fail,
        ConstructionResult.finalState]
      exact .refl state
  | ok rows =>
      rw [abandonPreservingExit_exact state id replacement indexed ⟨rows, checked⟩]
      apply (abandonRowsState_ownership_frame (protectedRows state id replacement) state ?_
        (protectedRows_indexed state id replacement indexed).2).2
      intro row member
      have original := (protectedRows_exact_selection state id replacement row).mp member
      obtain ⟨index, found⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp original.1)
      simpa only [indexed index row found] using found

end Goose.Proofs.ConstructionExecutionOwnership
