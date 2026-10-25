import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupAncestry
import Goose.Proofs.ConstructionExecutionOwnershipCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem abandonRowsState_use_lookup (rows : List PendingDestination) (state : ConstructionState)
    (current : ∀ row ∈ rows, state.destinations[row.capability.id]? = some row)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id)
    (id : DestinationId) (row : PendingDestination)
    (present : (abandonRowsState rows state).destinations[id]? = some row) :
    ∃ original, state.destinations[id]? = some original ∧ original.use = row.use := by
  induction rows generalizing state with
  | nil => exact ⟨row, present, rfl⟩
  | cons first rest ih =>
      let next : ConstructionState := {state with
        destinations := state.destinations.set! first.capability.id {first with progress := .abandoned}
        events := state.events ++ [.abandon first.capability.id]}
      have firstPresent := current first (List.mem_cons_self ..)
      have inside := (Array.getElem?_eq_some_iff.mp firstPresent).1
      obtain ⟨middle, middlePresent, sameUse⟩ := ih next (by
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
        exact ⟨first, firstPresent, sameUse⟩
      · exact ⟨middle, by simpa only [next, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne same] using middlePresent, sameUse⟩

theorem abandonRowsState_active_unchanged (rows : List PendingDestination) (state : ConstructionState)
    (id : DestinationId) (row : PendingDestination)
    (present : (abandonRowsState rows state).destinations[id]? = some row)
    (active : activeProgress row.progress = true) : state.destinations[id]? = some row := by
  induction rows generalizing state with
  | nil => exact present
  | cons first rest ih =>
      let next : ConstructionState := {state with
        destinations := state.destinations.set! first.capability.id {first with progress := .abandoned}
        events := state.events ++ [.abandon first.capability.id]}
      have found := ih next present
      by_cases same : first.capability.id = id
      · by_cases inside : id < state.destinations.size
        · have equal : {first with progress := .abandoned} = row := by
            simpa only [next, same, Array.set!_eq_setIfInBounds,
              Array.getElem?_setIfInBounds_self_of_lt inside, Option.some.injEq] using found
          subst row
          cases active
        · simpa only [next, same, Array.set!_eq_setIfInBounds,
            Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_gt inside)] using found
      · simpa only [next, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using found

theorem protectedRows_current (state : ConstructionState) (root final : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state) :
    ∀ row ∈ protectedRows state root final, state.destinations[row.capability.id]? = some row := by
  intro row member
  have selected := (protectedRows_exact_selection state root final row).mp member
  obtain ⟨id, present⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp selected.1)
  simpa only [indexed id row present] using present

theorem protectedCleanup_inactive (state : ConstructionState) (root final id : DestinationId)
    (original row : PendingDestination) (indexed : DestinationCapabilitiesIndexed state)
    (present : state.destinations[id]? = some original)
    (descendant : destinationDescendant state.destinations root id = true) (different : id ≠ final)
    (found : (abandonRowsState (protectedRows state root final) state).destinations[id]? = some row) :
    activeProgress row.progress = false := by
  have correct := indexed id original present
  obtain ⟨bounded, unique⟩ := protectedRows_indexed state root final indexed
  by_cases member : original ∈ protectedRows state root final
  · have selected := abandonRowsState_inside (protectedRows state root final) state bounded unique original member
    rw [correct] at selected
    have equal := Option.some.inj (found.symm.trans selected)
    subst row
    rfl
  · have outside : ∀ selected ∈ protectedRows state root final, selected.capability.id ≠ id := by
      intro selected included same
      have selectedPresent := protectedRows_current state root final indexed selected included
      rw [same] at selectedPresent
      have equal := Option.some.inj (selectedPresent.symm.trans present)
      subst selected
      exact member included
    rw [abandonRowsState_outside _ _ _ outside, present] at found
    cases Option.some.inj found
    cases active : activeProgress original.progress with
    | false => rfl
    | true =>
        apply False.elim
        apply member
        apply (protectedRows_exact_selection state root final original).mpr
        refine ⟨Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨id, present⟩), ?_, ?_, ?_⟩
        · simpa only [correct] using different
        · simpa only [correct] using descendant
        · cases progress : original.progress <;> simpa only [activeRow, progress, activeProgress] using active

end Goose.Proofs.ConstructionExecutionOwnership
