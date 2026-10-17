import Goose.Proofs.ConstructionExecutionProtocolOwnersAncestry
import Goose.Proofs.ConstructionExecutionProtocolCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

abbrev protectedCleanup (rows : List PendingDestination) : ConstructionM Unit := fun state =>
  match rows with
  | [] => (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
      (protectedAbandonment_nil_transition state)
  | row :: rest => (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
      (protectedAbandonment_cons_transition row rest state)

theorem protectedCleanup_nil (state : ConstructionState) :
    protectedCleanup [] state = .ok () state := protectedAbandonment_nil_transition state

theorem protectedCleanup_cons (row : PendingDestination) (rest : List PendingDestination)
    (state : ConstructionState) :
    protectedCleanup (row :: rest) state =
      if row.capability.id < state.destinations.size then
        protectedCleanup rest { state with
          destinations := state.destinations.set! row.capability.id { row with progress := .abandoned }
          events := state.events ++ [.abandon row.capability.id] }
      else .fault .destination state := by
  cases rest <;> simpa only [protectedCleanup] using protectedAbandonment_cons_transition row _ state

def abandonRowsState : List PendingDestination → ConstructionState → ConstructionState
  | [], state => state
  | row :: rest, state => abandonRowsState rest { state with
      destinations := state.destinations.set! row.capability.id { row with progress := .abandoned }
      events := state.events ++ [.abandon row.capability.id] }

theorem protectedCleanup_exact (rows : List PendingDestination) (state : ConstructionState)
    (bounded : ∀ row ∈ rows, row.capability.id < state.destinations.size) :
    protectedCleanup rows state = .ok () (abandonRowsState rows state) := by
  induction rows generalizing state with
  | nil => exact protectedCleanup_nil state
  | cons row rest ih =>
      rw [protectedCleanup_cons, ite_eq_left (bounded row (List.mem_cons_self ..))]
      apply ih
      intro next member
      simpa using bounded next (List.mem_cons_of_mem _ member)

theorem abandonRowsState_frame (rows : List PendingDestination) (state : ConstructionState) :
    (abandonRowsState rows state).storage = state.storage ∧
    (abandonRowsState rows state).stdout = state.stdout ∧
    (abandonRowsState rows state).destinations.size = state.destinations.size ∧
    (abandonRowsState rows state).events =
      state.events ++ rows.map (fun row => ConstructionEvent.abandon row.capability.id) := by
  induction rows generalizing state with
  | nil => simp [abandonRowsState]
  | cons row rest ih =>
      simpa [abandonRowsState, List.append_assoc] using ih { state with
        destinations := state.destinations.set! row.capability.id { row with progress := .abandoned }
        events := state.events ++ [.abandon row.capability.id] }

theorem abandonRowsState_outside (rows : List PendingDestination) (state : ConstructionState)
    (index : DestinationId) (outside : ∀ row ∈ rows, row.capability.id ≠ index) :
    (abandonRowsState rows state).destinations[index]? = state.destinations[index]? := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih =>
      rw [abandonRowsState, ih _ (by intro next member; exact outside next (List.mem_cons_of_mem _ member))]
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne
        (outside row (List.mem_cons_self ..))]

theorem abandonRowsState_inside (rows : List PendingDestination) (state : ConstructionState)
    (bounded : ∀ row ∈ rows, row.capability.id < state.destinations.size)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id)
    (row : PendingDestination) (member : row ∈ rows) :
    (abandonRowsState rows state).destinations[row.capability.id]? =
      some { row with progress := .abandoned } := by
  induction rows generalizing state with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst row
        rw [abandonRowsState, abandonRowsState_outside]
        · simp [Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_self_of_lt (bounded first (List.mem_cons_self ..))]
        · intro next member
          exact Ne.symm ((List.pairwise_cons.mp unique).1 next member)
      · apply ih _ (by intro next member; simpa using bounded next (List.mem_cons_of_mem _ member))
          (List.pairwise_cons.mp unique).2 later

def activeRow (row : PendingDestination) : Bool :=
  match row.progress with
  | .open _ | .suspended _ _ | .built _ | .exiting _ _ => true
  | .published _ | .attached _ | .abandoned | .cancelled | .retired => false

def protectedRows (state : ConstructionState) (id replacement : DestinationId) : List PendingDestination :=
  state.destinations.toList.reverse.filter fun row =>
    row.capability.id != replacement &&
      destinationDescendant state.destinations id row.capability.id && activeRow row

theorem protectedRows_exact_selection (state : ConstructionState) (id replacement : DestinationId)
    (row : PendingDestination) :
    row ∈ protectedRows state id replacement ↔ row ∈ state.destinations.toList ∧
      row.capability.id ≠ replacement ∧
      destinationDescendant state.destinations id row.capability.id = true ∧ activeRow row = true := by
  simp [protectedRows, and_assoc]

theorem protectedRows_indexed (state : ConstructionState) (id replacement : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state) :
    (∀ row ∈ protectedRows state id replacement, row.capability.id < state.destinations.size) ∧
    (protectedRows state id replacement).Pairwise
      (fun first second => first.capability.id ≠ second.capability.id) := by
  constructor
  · intro row member
    have present := (protectedRows_exact_selection state id replacement row).mp member
    obtain ⟨index, found⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp present.1)
    have correct := indexed index row found
    simpa [correct] using (Array.getElem?_eq_some_iff.mp found).1
  · apply List.Pairwise.filter
    apply List.pairwise_reverse.mpr
    have unique : (state.destinations.toList.map (·.capability.id)).Nodup := by
      rw [destination_capability_ids_eq_range state indexed]
      exact List.nodup_range
    exact (List.pairwise_map.mp unique).imp (by intro first second different; exact Ne.symm different)

theorem protectedExitDiscarded_exact (state : ConstructionState) (id replacement : DestinationId)
    (rows : List PendingDestination)
    (checked : protectedExitDiscarded state id replacement = .ok rows) :
    rows = protectedRows state id replacement := by
  simp only [protectedExitDiscarded, bind, pure, Except.bind, Except.pure] at checked
  repeat' first
    | contradiction
    | simp only [Except.bind, Except.pure] at checked
    | split at checked
  all_goals
    have equal := Except.ok.inj checked
    subst rows
    rfl

theorem abandonPreservingExit_exact (state : ConstructionState) (id replacement : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state)
    (checked : ∃ rows, protectedExitDiscarded state id replacement = .ok rows) :
    abandonPreservingExit id replacement state =
      .ok () (abandonRowsState (protectedRows state id replacement) state) := by
  obtain ⟨rows, checked⟩ := checked
  have selected := protectedExitDiscarded_exact state id replacement rows checked
  have bounded := (protectedRows_indexed state id replacement indexed).1
  simp only [abandonPreservingExit, ConstructionM.get, bind, checked]
  have exactResult := protectedCleanup_exact rows state (by simpa [selected] using bounded)
  cases rows with
  | nil => simpa only [protectedCleanup, selected] using exactResult
  | cons row rest => simpa only [protectedCleanup, selected] using exactResult

theorem abandonPreservingExit_selected_row (state : ConstructionState) (id replacement : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state)
    (checked : ∃ rows, protectedExitDiscarded state id replacement = .ok rows)
    (row : PendingDestination) (member : row ∈ state.destinations.toList)
    (different : row.capability.id ≠ replacement)
    (descendant : destinationDescendant state.destinations id row.capability.id = true)
    (active : activeRow row = true) :
    (abandonPreservingExit id replacement state).finalState.destinations[row.capability.id]? =
      some { row with progress := .abandoned } := by
  rw [abandonPreservingExit_exact state id replacement indexed checked]
  apply abandonRowsState_inside
  · exact (protectedRows_indexed state id replacement indexed).1
  · exact (protectedRows_indexed state id replacement indexed).2
  · exact (protectedRows_exact_selection state id replacement row).mpr
      ⟨member, different, descendant, active⟩

theorem abandonPreservingExit_replacement_untouched (state : ConstructionState)
    (id replacement : DestinationId) (indexed : DestinationCapabilitiesIndexed state)
    (checked : ∃ rows, protectedExitDiscarded state id replacement = .ok rows) :
    (abandonPreservingExit id replacement state).finalState.destinations[replacement]? =
      state.destinations[replacement]? := by
  rw [abandonPreservingExit_exact state id replacement indexed checked]
  apply abandonRowsState_outside
  intro row member
  exact ((protectedRows_exact_selection state id replacement row).mp member).2.1

theorem abandonPreservingExit_exact_events (state : ConstructionState) (id replacement : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state)
    (checked : ∃ rows, protectedExitDiscarded state id replacement = .ok rows) :
    (abandonPreservingExit id replacement state).finalState.events = state.events ++
      (protectedRows state id replacement).map (fun row => .abandon row.capability.id) := by
  rw [abandonPreservingExit_exact state id replacement indexed checked]
  exact (abandonRowsState_frame _ _).2.2.2

theorem protectedRows_abandon_events_unique (state : ConstructionState) (id replacement : DestinationId)
    (indexed : DestinationCapabilitiesIndexed state) :
    ((protectedRows state id replacement).map
      (fun row => ConstructionEvent.abandon row.capability.id)).Nodup := by
  apply List.pairwise_map.mpr
  apply ((protectedRows_indexed state id replacement indexed).2).imp
  intro first second different equal
  exact different (ConstructionEvent.abandon.inj equal)

theorem destinationDescendant_self (state : ConstructionState) (id : DestinationId)
    (inside : id < state.destinations.size) :
    destinationDescendant state.destinations id id = true := by
  dsimp only [destinationDescendant]
  rw [descendantOf_result]
  cases sizeEq : state.destinations.size with
  | zero => simp [sizeEq] at inside
  | succ size =>
      simp [Std.Legacy.Range.forIn_eq_forIn_range', List.range'_succ, List.forIn_cons, pure]
      rfl

end Goose.Proofs.ConstructionExecutionOwnership
