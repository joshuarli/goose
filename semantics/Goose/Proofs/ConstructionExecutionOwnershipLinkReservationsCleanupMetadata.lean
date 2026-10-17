import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupRows

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem abandonRowsState_metadata_lookup (rows : List PendingDestination) (state : ConstructionState)
    (current : ∀ row ∈ rows, state.destinations[row.capability.id]? = some row)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id)
    (id : DestinationId) (row : PendingDestination)
    (present : (abandonRowsState rows state).destinations[id]? = some row) :
    ∃ original, state.destinations[id]? = some original ∧
      {row with progress := original.progress} = original ∧
      (row.progress = original.progress ∨ row.progress = .abandoned) := by
  induction rows generalizing state with
  | nil => exact ⟨row, present, rfl, Or.inl rfl⟩
  | cons first rest ih =>
      let next : ConstructionState := {state with
        destinations := state.destinations.set! first.capability.id {first with progress := .abandoned}
        events := state.events ++ [.abandon first.capability.id]}
      have firstPresent := current first (List.mem_cons_self ..)
      have inside := (Array.getElem?_eq_some_iff.mp firstPresent).1
      obtain ⟨middle, middlePresent, metadata, phase⟩ := ih next (by
        intro nextRow member
        have different := (List.pairwise_cons.mp unique).1 nextRow member
        simpa only [next, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different]
          using current nextRow (List.mem_cons_of_mem _ member)) (List.pairwise_cons.mp unique).2 present
      by_cases same : first.capability.id = id
      · subst id
        have equal : {first with progress := .abandoned} = middle := by
          simpa only [next, Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_self_of_lt inside, Option.some.injEq] using middlePresent
        subst middle
        refine ⟨first, firstPresent, ?_, Or.inr ?_⟩
        · exact congrArg (fun current : PendingDestination => {current with progress := first.progress}) metadata
        · rcases phase with same | abandoned
          · exact same
          · exact abandoned
      · exact ⟨middle, by simpa only [next, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne same] using middlePresent, metadata, phase⟩


end Goose.Proofs.ConstructionExecutionOwnership
