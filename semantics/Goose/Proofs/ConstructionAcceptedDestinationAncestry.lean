import Goose.Proofs.ConstructionAcceptedDestinationFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (DestinationId)
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership

private theorem walk_succ (rows : Array PendingDestination) (ancestor fuel id : Nat) :
    ancestryWalk rows ancestor (fuel + 1) id =
      if id == ancestor then true else match rows[id]? with
      | none => false
      | some row => match row.use with
        | .receiver => false
        | .child parent | .replacement parent => ancestryWalk rows ancestor fuel parent := rfl

private theorem walk_fuel (state : ConstructionState) (ordered : DestinationOwnersOrdered state)
    (ancestor first second id : Nat) (firstBound : id < first) (secondBound : id < second) :
    ancestryWalk state.destinations ancestor first id = ancestryWalk state.destinations ancestor second id := by
  induction first generalizing second id with
  | zero => omega
  | succ first ih =>
    cases second with
    | zero => omega
    | succ second =>
      rw [walk_succ, walk_succ]
      split
      · rfl
      · cases found : state.destinations[id]? with
        | none => rfl
        | some row =>
          simp only
          cases use : row.use with
          | receiver => rfl
          | child parent | replacement parent =>
            simp only
            have earlier : parent < id := by simpa only [use] using ordered id row found
            exact ih second parent (Nat.lt_of_lt_of_le earlier (Nat.le_of_lt_succ firstBound))
              (Nat.lt_of_lt_of_le earlier (Nat.le_of_lt_succ secondBound))

private theorem walk_push_old (state : ConstructionState) (ordered : DestinationOwnersOrdered state)
    (added : PendingDestination) (ancestor fuel id : Nat) (inside : id < state.destinations.size) :
    ancestryWalk (state.destinations.push added) ancestor fuel id = ancestryWalk state.destinations ancestor fuel id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
    rw [walk_succ, walk_succ]
    simp only [Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte]
    split
    · rfl
    · cases found : state.destinations[id]? with
      | none => rfl
      | some row =>
        simp only
        cases use : row.use with
        | receiver => rfl
        | child parent | replacement parent =>
          simp only
          have earlier : parent < id := by simpa only [use] using ordered id row found
          exact ih parent (Nat.lt_trans earlier inside)

theorem FreshDestinationFrame.ancestry {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (ordered : DestinationOwnersOrdered before.construction) (ancestor id : Nat)
    (inside : ancestor < before.construction.destinations.size) :
    destinationDescendant after.construction.destinations ancestor id =
      destinationDescendant before.construction.destinations ancestor id := by
  rw [frame.destinations, destinationDescendant_walk, destinationDescendant_walk, Array.size_push]
  by_cases old : id < before.construction.destinations.size
  · rw [walk_push_old before.construction ordered frame.row ancestor _ id old]
    exact walk_fuel before.construction ordered ancestor _ _ id (by omega) old
  · have positive : 0 < before.construction.destinations.size := by omega
    obtain ⟨fuel, count⟩ : ∃ fuel, before.construction.destinations.size = fuel + 1 := ⟨before.construction.destinations.size - 1, by omega⟩
    rw [count, walk_succ, walk_succ]
    have different : (id == ancestor) = false := by simp; omega
    rw [different]
    have absent : before.construction.destinations[id]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
    rw [absent]
    by_cases last : id = before.construction.destinations.size
    · subst id
      simp only [Array.getElem?_push_size, frame.receiver]
    · simp only [Array.getElem?_push, last, ↓reduceIte, absent]

#print axioms FreshDestinationFrame.ancestry

end Goose.Proofs.ConstructionAcceptedExecution
