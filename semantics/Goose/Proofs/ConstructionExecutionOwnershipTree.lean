import Goose.Proofs.ConstructionExecutionOwnershipCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

def abandonRowState (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (storage : ReceivingStorage) : ConstructionState :=
  { state with
    storage := state.storage.set! destination.storage
      { storage with bytes := storage.bytes.extract 0 destination.rollbackEnd }
    destinations := state.destinations.set! id { destination with progress := .abandoned }
    events := state.events ++ [.abandon id] }

theorem abandonDestination_exact (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (storage : ReceivingStorage)
    (present : state.destinations[id]? = some destination)
    (writable : destinationCanWrite state id = true)
    (unfinished : ∃ count, destination.progress = .open count ∨ destination.progress = .built count)
    (stored : state.storage[destination.storage]? = some storage) :
    abandonDestination id state = .ok () (abandonRowState state id destination storage) := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  obtain ⟨count, progress | progress⟩ := unfinished
  all_goals
    simp only [abandonDestination, writableDestination_result, present, writable, progress,
      lookupStorage_result, stored, replaceStorage_result, replaceDestination_result,
      emit_result, bind, storageInside, inside, ↓reduceIte, abandonRowState]

abbrev treeRows (state : ConstructionState) (id : DestinationId) : List PendingDestination :=
  state.destinations.toList.reverse.filter fun row =>
    destinationDescendant state.destinations id row.capability.id && activeRow row

theorem treeRows_exact_selection (state : ConstructionState) (id : DestinationId)
    (row : PendingDestination) :
    row ∈ treeRows state id ↔ row ∈ state.destinations.toList ∧
      destinationDescendant state.destinations id row.capability.id = true ∧ activeRow row = true := by
  simp [treeRows, Bool.and_eq_true_iff]

theorem abandonDestination_preserves_published_count (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (storage : ReceivingStorage)
    (present : state.destinations[id]? = some destination)
    (writable : destinationCanWrite state id = true)
    (unfinished : ∃ count, destination.progress = .open count ∨ destination.progress = .built count)
    (stored : state.storage[destination.storage]? = some storage) :
    ((abandonDestination id state).finalState.storage[destination.storage]?).map (·.publishedCount) =
      some storage.publishedCount := by
  rw [abandonDestination_exact state id destination storage present writable unfinished stored]
  have inside := (Array.getElem?_eq_some_iff.mp stored).1
  simp [abandonRowState, ConstructionResult.finalState, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_self_of_lt inside]

private abbrev writableStep (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (writableDestination_result id state)

private abbrev replaceStep (id : DestinationId) (row : PendingDestination) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (replaceDestination_result id row state)

def treeCleanupStep (row : PendingDestination) : ConstructionM Unit := do
  let current ← writableStep row.capability.id
  match current.progress with
  | .suspended count _ => replaceStep current.capability.id { current with progress := .open count }
  | _ => pure ()
  abandonDestination row.capability.id

def treeAbandonRowState (state : ConstructionState) (row : PendingDestination) : ConstructionState :=
  { state with
    storage := state.storage.modify row.storage fun storage =>
      { storage with bytes := storage.bytes.extract 0 row.rollbackEnd }
    destinations := state.destinations.set! row.capability.id { row with progress := .abandoned }
    events := state.events ++ [.abandon row.capability.id] }

private theorem storage_progress (row : PendingDestination) (progress : DestinationProgress) :
    ({ row with progress := progress } : PendingDestination).storage = row.storage := rfl

set_option maxHeartbeats 1000000 in
theorem treeCleanupStep_success (state final : ConstructionState) (row : PendingDestination)
    (present : state.destinations[row.capability.id]? = some row)
    (result : treeCleanupStep row state = .ok () final) :
    final = treeAbandonRowState state row := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  simp only [treeCleanupStep, writableStep, writableDestination_result, present, bind] at result
  cases writable : destinationCanWrite state row.capability.id with
  | false => simp [writable] at result
  | true =>
      simp only [writable] at result
      cases progress : row.progress <;>
        simp only [progress, pure, bind, replaceStep, replaceDestination_result, inside, ↓reduceIte] at result
      case suspended count child =>
        let reopened := { row with progress := DestinationProgress.open count }
        let next := { state with destinations := state.destinations.set! row.capability.id reopened }
        have current : next.destinations[row.capability.id]? = some reopened :=
          Array.getElem?_setIfInBounds_self_of_lt inside
        change abandonDestination row.capability.id next = .ok () final at result
        cases allowed : destinationCanWrite next row.capability.id with
        | false => simp [abandonDestination, writableDestination_result, current, allowed, bind] at result
        | true =>
            cases stored : state.storage[row.storage]? with
            | none =>
                have storedNext : next.storage[reopened.storage]? = none := stored
                simp only [abandonDestination, writableDestination_result, current, allowed, bind] at result
                have reopenedProgress : reopened.progress = .open count := rfl
                simp only [reopenedProgress, lookupStorage_result, storedNext] at result
                contradiction
            | some storage =>
                have storedNext : next.storage[reopened.storage]? = some storage := stored
                rw [abandonDestination_exact next row.capability.id reopened storage current allowed
                  ⟨count, Or.inl rfl⟩ storedNext] at result
                cases result
                simp only [abandonRowState, treeAbandonRowState, next, reopened, storage_progress,
                  Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]
                simp [Array.modify, Array.modifyM, Array.setIfInBounds,
                  (Array.getElem?_eq_some_iff.mp stored).1, (Array.getElem?_eq_some_iff.mp stored).2]
      all_goals
        cases stored : state.storage[row.storage]? with
        | none =>
            simp [abandonDestination, writableDestination_result, present, writable,
              progress, lookupStorage_result, stored, bind, ConstructionM.fail] at result
        | some storage =>
            simp only [abandonDestination, writableDestination_result, present, writable,
              progress, lookupStorage_result, stored, bind, replaceStorage_result,
              replaceDestination_result, emit_result, inside,
              (Array.getElem?_eq_some_iff.mp stored).1, ↓reduceIte] at result
            first
            | contradiction
            | cases result
              simp [treeAbandonRowState, Array.modify, Array.modifyM, stored,
                (Array.getElem?_eq_some_iff.mp stored).1, (Array.getElem?_eq_some_iff.mp stored).2,
                Array.set!_eq_setIfInBounds, Array.setIfInBounds]

def treeCleanupLoop : List PendingDestination → ConstructionM Unit
  | [] => pure ()
  | row :: rest => do
      treeCleanupStep row
      treeCleanupLoop rest

def treeAbandonRowsState : List PendingDestination → ConstructionState → ConstructionState
  | [], state => state
  | row :: rest, state => treeAbandonRowsState rest (treeAbandonRowState state row)

theorem treeCleanupLoop_success (rows : List PendingDestination) (state final : ConstructionState)
    (current : ∀ row ∈ rows, state.destinations[row.capability.id]? = some row)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id)
    (result : treeCleanupLoop rows state = .ok () final) :
    final = treeAbandonRowsState rows state := by
  induction rows generalizing state with
  | nil => cases result; rfl
  | cons row rest ih =>
      simp only [treeCleanupLoop, bind] at result
      cases first : treeCleanupStep row state with
      | fault kind after => simp only [first] at result; contradiction
      | ok token after =>
          cases token
          have step := treeCleanupStep_success state after row (current row (List.mem_cons_self ..)) first
          simp only [first] at result
          subst after
          apply ih _ _ (List.pairwise_cons.mp unique).2 result
          intro next member
          have different := (List.pairwise_cons.mp unique).1 next member
          simpa only [treeAbandonRowState, Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_ne different] using current next (List.mem_cons_of_mem _ member)

private theorem abandonRows_destinations_congr (rows : List PendingDestination)
    (before after : ConstructionState) (destinations : before.destinations = after.destinations) :
    (abandonRowsState rows before).destinations = (abandonRowsState rows after).destinations := by
  induction rows generalizing before after with
  | nil => exact destinations
  | cons row rest ih =>
      apply ih
      simp only [destinations]

theorem treeAbandonRowsState_destinations (rows : List PendingDestination) (state : ConstructionState) :
    (treeAbandonRowsState rows state).destinations = (abandonRowsState rows state).destinations := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih =>
      rw [treeAbandonRowsState, ih]
      apply abandonRows_destinations_congr
      rfl

theorem treeAbandonRowsState_events (rows : List PendingDestination) (state : ConstructionState) :
    (treeAbandonRowsState rows state).events =
      state.events ++ rows.map (fun row => ConstructionEvent.abandon row.capability.id) := by
  induction rows generalizing state with
  | nil => simp [treeAbandonRowsState]
  | cons row rest ih =>
      simpa [treeAbandonRowsState, treeAbandonRowState, List.append_assoc] using
        (ih (treeAbandonRowState state row))

def treeForIn (rows : List PendingDestination) : ConstructionM Unit := do
  for row in rows do treeCleanupStep row

theorem treeForIn_eq_loop (rows : List PendingDestination) : treeForIn rows = treeCleanupLoop rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      funext state
      simp only [treeForIn, List.forIn_cons, treeCleanupLoop, bind]
      cases first : treeCleanupStep row state with
      | fault kind after => rfl
      | ok token after =>
          simpa only [treeForIn, bind, pure] using congrFun ih after

private abbrev treeSourceBody (row : PendingDestination) (_ : PUnit.{1}) : ConstructionM (ForInStep PUnit) := do
  let current ← writableStep row.capability.id
  match current.progress with
  | .suspended count _ => replaceStep current.capability.id { current with progress := .open count }
  | _ => pure ()
  abandonDestination row.capability.id
  pure (.yield PUnit.unit)

private theorem treeSourceBody_eq (row : PendingDestination) (token : PUnit.{1}) :
    treeSourceBody row token = (treeCleanupStep row >>= fun _ => pure (.yield PUnit.unit)) := by
  funext state
  simp only [treeSourceBody, treeCleanupStep, bind]
  cases first : writableStep row.capability.id state with
  | fault kind after => rfl
  | ok current after =>
      cases progress : current.progress <;> simp only [progress] <;> try rfl
      case suspended count child =>
        cases replaced : replaceStep current.capability.id { current with progress := .open count } after <;> rfl

private abbrev treeActualSourceBody (row : PendingDestination) (_ : PUnit.{1}) : ConstructionM (ForInStep PUnit) := do
  let current ← writableStep row.capability.id
  match current.progress with
  | .suspended count _ =>
      replaceStep current.capability.id { current with progress := .open count }
      abandonDestination row.capability.id
      pure (.yield PUnit.unit)
  | _ =>
      abandonDestination row.capability.id
      pure (.yield PUnit.unit)

private theorem treeActualSourceBody_eq : treeActualSourceBody = treeSourceBody := by
  funext row token state
  simp only [treeActualSourceBody, treeSourceBody, bind]
private abbrev treeSourceLoop (rows : List PendingDestination) : ConstructionM Unit := do
  let _ ← forIn rows PUnit.unit treeSourceBody
  pure ()

private theorem treeSourceLoop_eq (rows : List PendingDestination) :
    treeSourceLoop rows = treeCleanupLoop rows := by
  rw [← treeForIn_eq_loop]
  have bodies : treeSourceBody = fun row _ => treeCleanupStep row >>= fun _ => pure (.yield PUnit.unit) := by
    funext row token
    exact treeSourceBody_eq row token
  simp only [treeSourceLoop, treeForIn, bodies]

private abbrev treeCheckBody (row : PendingDestination) (_ : PUnit.{1}) : ConstructionM (ForInStep PUnit) :=
  match row.progress with
  | .exiting _ _ => ConstructionM.fail .protocol
  | _ => pure (.yield PUnit.unit)

private abbrev treeCheckLoop (rows : List PendingDestination) : ConstructionM PUnit :=
  forIn rows PUnit.unit treeCheckBody

private theorem treeCheckLoop_state (rows : List PendingDestination) (state : ConstructionState) :
    (treeCheckLoop rows state).finalState = state := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [treeCheckLoop, List.forIn_cons, treeCheckBody, bind]
      cases row.progress <;> try rfl
      all_goals simpa only [treeCheckLoop, pure, bind, ConstructionM.fail, ConstructionResult.finalState] using ih

theorem treeRows_indexed (state : ConstructionState) (id : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state) :
    (∀ row ∈ treeRows state id, state.destinations[row.capability.id]? = some row) ∧
    (treeRows state id).Pairwise (fun first second => first.capability.id ≠ second.capability.id) := by
  constructor
  · intro row member
    have original := ((treeRows_exact_selection state id row).mp member).1
    obtain ⟨index, present⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp original)
    simpa only [indexed index row present] using present
  · apply List.Pairwise.filter
    apply List.pairwise_reverse.mpr
    have unique : (state.destinations.toList.map (·.capability.id)).Nodup := by
      rw [destination_capability_ids_eq_range state indexed]
      exact List.nodup_range
    exact (List.pairwise_map.mp unique).imp (by intro first second different; exact Ne.symm different)

set_option maxHeartbeats 1000000 in
theorem abandonTree_success_exact (state final : ConstructionState) (id : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state)
    (result : abandonTree id state = .ok () final) :
    final = treeAbandonRowsState (treeRows state id) state := by
  simp only [abandonTree, bind] at result
  rw [writableDestination_result id state] at result
  cases present : state.destinations[id]? with
  | none => simp only [present] at result; contradiction
  | some destination =>
      simp only [present] at result
      cases writable : destinationCanWrite state id with
      | false => simp only [writable] at result; contradiction
      | true =>
          simp only [writable] at result
          cases progress : destination.progress <;>
            simp only [progress, pure, bind, ConstructionM.get, ConstructionM.fail] at result <;>
            try contradiction
          all_goals
            change ((treeCheckLoop (treeRows state id) >>= fun _ => (do
              let _ ← forIn (treeRows state id) PUnit.unit treeActualSourceBody
              pure ())) state) =
              .ok () final at result
            rw [treeActualSourceBody_eq] at result
            change ((treeCheckLoop (treeRows state id) >>= fun _ => treeSourceLoop (treeRows state id)) state) =
              .ok () final at result
            have unchanged := treeCheckLoop_state (treeRows state id) state
            simp only [bind] at result
            cases checked : treeCheckLoop (treeRows state id) state with
            | fault kind after => simp only [checked] at result; contradiction
            | ok token after =>
                simp only [checked, ConstructionResult.finalState] at unchanged
                subst after
                simp only [checked, treeSourceLoop_eq] at result
                apply treeCleanupLoop_success (treeRows state id) state final
                · exact (treeRows_indexed state id indexed).1
                · exact (treeRows_indexed state id indexed).2
                · exact result

theorem treeAbandonRowsState_stdout (rows : List PendingDestination) (state : ConstructionState) :
    (treeAbandonRowsState rows state).stdout = state.stdout := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih => exact ih (treeAbandonRowState state row)

private theorem treeAbandonRowState_published_counts (state : ConstructionState) (row : PendingDestination) :
    (treeAbandonRowState state row).storage.map (·.publishedCount) = state.storage.map (·.publishedCount) := by
  apply Array.ext_getElem?
  intro index
  simp only [treeAbandonRowState, Array.getElem?_map, Array.getElem?_modify]
  split
  · cases state.storage[index]? <;> rfl
  · rfl

theorem treeAbandonRowsState_published_counts (rows : List PendingDestination) (state : ConstructionState) :
    (treeAbandonRowsState rows state).storage.map (·.publishedCount) = state.storage.map (·.publishedCount) := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih =>
      exact (ih (treeAbandonRowState state row)).trans (treeAbandonRowState_published_counts state row)

theorem abandonTree_success_selected_row (state final : ConstructionState) (id : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state) (result : abandonTree id state = .ok () final)
    (row : PendingDestination) (member : row ∈ state.destinations.toList)
    (descendant : destinationDescendant state.destinations id row.capability.id = true)
    (active : activeRow row = true) :
    final.destinations[row.capability.id]? = some { row with progress := .abandoned } := by
  rw [abandonTree_success_exact state final id indexed result, treeAbandonRowsState_destinations]
  have rowsCurrent := (treeRows_indexed state id indexed).1
  apply abandonRowsState_inside
  · intro next member
    exact (Array.getElem?_eq_some_iff.mp (rowsCurrent next member)).1
  · exact (treeRows_indexed state id indexed).2
  · exact (treeRows_exact_selection state id row).mpr ⟨member, descendant, active⟩

theorem abandonTree_success_outside (state final : ConstructionState) (id index : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state) (result : abandonTree id state = .ok () final)
    (outside : ∀ row ∈ treeRows state id, row.capability.id ≠ index) :
    final.destinations[index]? = state.destinations[index]? := by
  rw [abandonTree_success_exact state final id indexed result, treeAbandonRowsState_destinations]
  exact abandonRowsState_outside _ _ index outside

theorem abandonTree_success_events_unique (state : ConstructionState) (id : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state) :
    ((treeRows state id).map (fun row => ConstructionEvent.abandon row.capability.id)).Nodup := by
  apply List.pairwise_map.mpr
  apply ((treeRows_indexed state id indexed).2).imp
  intro first second different equal
  exact different (ConstructionEvent.abandon.inj equal)

end Goose.Proofs.ConstructionExecutionOwnership
