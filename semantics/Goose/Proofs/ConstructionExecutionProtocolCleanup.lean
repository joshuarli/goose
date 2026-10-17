import Goose.Proofs.ConstructionExecutionProtocolAbandon

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private def RowActive (destination : PendingDestination) : Prop :=
  ∃ count, destination.progress = .open count ∨ destination.progress = .built count ∨
    (∃ child, destination.progress = .suspended count child) ∨
    ∃ replacement, destination.progress = .exiting count replacement

private theorem indexed_rows_current (state : ConstructionState)
    (valid : DestinationCapabilitiesIndexed state) (destination : PendingDestination)
    (member : destination ∈ state.destinations.toList) :
    state.destinations[destination.capability.id]? = some destination := by
  obtain ⟨index, present⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  simpa only [valid index destination present] using present

private theorem indexed_rows_unique (state : ConstructionState)
    (valid : DestinationCapabilitiesIndexed state) (predicate : PendingDestination → Bool) :
    (state.destinations.toList.reverse.filter predicate).Pairwise
      (fun first second => first.capability.id ≠ second.capability.id) := by
  apply List.Pairwise.filter
  apply List.pairwise_reverse.mpr
  have unique : (state.destinations.toList.map (·.capability.id)).Nodup := by
    rw [destination_capability_ids_eq_range state valid]
    exact List.nodup_range
  exact (List.pairwise_map.mp unique).imp (by intro first second different; exact Ne.symm different)

theorem destinationLifecycleInvariant_abandon_rows
    (action : List PendingDestination → ConstructionM Unit)
    (nilResult : ∀ state, action [] state = .ok () state)
    (consResult : ∀ destination rest state,
      action (destination :: rest) state =
        if destination.capability.id < state.destinations.size then
          action rest { state with
            destinations := state.destinations.set! destination.capability.id
              { destination with progress := .abandoned }
            events := state.events ++ [.abandon destination.capability.id] }
        else .fault .destination state)
    (rows : List PendingDestination) (state : ConstructionState)
    (current : ∀ destination ∈ rows,
      state.destinations[destination.capability.id]? = some destination)
    (active : ∀ destination ∈ rows, RowActive destination)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (action rows state).finalState := by
  induction rows generalizing state with
  | nil => simpa only [nilResult, ConstructionResult.finalState] using valid
  | cons destination rest ih =>
      have present := current destination (List.mem_cons_self ..)
      have inside := (Array.getElem?_eq_some_iff.mp present).choose
      rw [consResult, if_pos inside]
      apply ih
      · intro next member
        have different := (List.pairwise_cons.mp unique).1 next member
        simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
          different, ↓reduceIte] using current next (List.mem_cons_of_mem _ member)
      · intro next member
        exact active next (List.mem_cons_of_mem _ member)
      · exact (List.pairwise_cons.mp unique).2
      · exact destinationLifecycleInvariant_abandon_row state destination.capability.id destination present
          (active destination (List.mem_cons_self ..)) valid

private def rowActiveBoolean (destination : PendingDestination) : Bool :=
  match destination.progress with
  | .open _ | .suspended _ _ | .built _ | .exiting _ _ => true
  | .published _ | .attached _ | .abandoned | .cancelled | .retired => false

private theorem active_of_boolean (destination : PendingDestination)
    (active : rowActiveBoolean destination = true) : RowActive destination := by
  cases progress : destination.progress <;> simp_all [rowActiveBoolean, RowActive]

private theorem protected_rows_valid (state : ConstructionState) (id replacementId : DestinationId)
    (rows : List PendingDestination)
    (checked : protectedExitDiscarded state id replacementId = .ok rows)
    (valid : DestinationCapabilitiesIndexed state) :
    (∀ destination ∈ rows, state.destinations[destination.capability.id]? = some destination) ∧
    (∀ destination ∈ rows, RowActive destination) ∧
    rows.Pairwise (fun first second => first.capability.id ≠ second.capability.id) := by
  simp only [protectedExitDiscarded, bind, pure, Except.bind, Except.pure] at checked
  repeat' first
    | contradiction
    | simp only [Except.bind, Except.pure] at checked
    | solve
      | cases checked
        refine ⟨?_, ?_, indexed_rows_unique state valid _⟩
        · intro destination member
          exact indexed_rows_current state valid destination
            (List.mem_reverse.mp (List.mem_filter.mp member).1)
        · intro destination member
          apply active_of_boolean destination
          exact (Bool.and_eq_true_iff.mp (List.mem_filter.mp member).2).2
    | split at checked

theorem abandonPreservingExit_destination_lifecycle_invariant (id replacementId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (abandonPreservingExit id replacementId state).finalState := by
  simp only [abandonPreservingExit, ConstructionM.get, bind]
  cases checked : protectedExitDiscarded state id replacementId with
  | error fault => exact valid
  | ok rows =>
      have rowsValid := protected_rows_valid state id replacementId rows checked valid.2.1
      apply destinationLifecycleInvariant_abandon_rows
      · exact protectedAbandonment_nil_transition
      · exact protectedAbandonment_cons_transition
      · exact rowsValid.1
      · exact rowsValid.2.1
      · exact rowsValid.2.2
      · exact valid

end Goose.Proofs.ConstructionExecutionProtocol
