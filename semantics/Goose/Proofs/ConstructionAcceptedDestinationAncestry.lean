import Goose.Proofs.ConstructionAcceptedDestinationFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (DestinationId)
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership

open Lean Elab Term Meta in
elab "fresh_destination_walk_fact" : term => do
  let info ← getConstInfo ``OwnershipReplacementPath.descendant
  let some value := info.value? (allowOpaque := true) | throwError "missing replacement ancestry proof"
  let some head := value.find? (fun term => match term with
    | .const name _ => name.toString.endsWith ".destinationDescendant_walk"
    | _ => false) | throwError "missing ancestry walk equation"
  pure head

open Lean Elab Term Meta in
elab "fresh_destination_walk" : term => do
  let info ← getConstInfo ``OwnershipReplacementPath.descendant
  let some value := info.value? (allowOpaque := true) | throwError "missing replacement ancestry proof"
  let some (.const name _) := value.find? (fun term => match term with
    | .const name _ => name.toString.endsWith ".destinationDescendant_walk"
    | _ => false) | throwError "missing ancestry walk equation"
  let equation ← getConstInfo name
  let some walk := equation.type.find? (fun term => match term with
    | .const name _ => name.toString.endsWith ".ancestryWalk"
    | _ => false) | throwError "missing ancestry walk"
  pure walk

private abbrev ancestorWalk : Array PendingDestination → Nat → Nat → Nat → Bool := fresh_destination_walk

private theorem descendant_walk (rows : Array PendingDestination) (ancestor id : Nat) :
    destinationDescendant rows ancestor id = ancestorWalk rows ancestor rows.size id := fresh_destination_walk_fact rows ancestor id

private theorem walk_succ (rows : Array PendingDestination) (ancestor fuel id : Nat) :
    ancestorWalk rows ancestor (fuel + 1) id =
      if id == ancestor then true else match rows[id]? with
      | none => false
      | some row => match row.use with
        | .receiver => false
        | .child parent | .replacement parent => ancestorWalk rows ancestor fuel parent := rfl

private theorem walk_fuel (state : ConstructionState) (ordered : DestinationOwnersOrdered state)
    (ancestor first second id : Nat) (firstBound : id < first) (secondBound : id < second) :
    ancestorWalk state.destinations ancestor first id = ancestorWalk state.destinations ancestor second id := by
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
    ancestorWalk (state.destinations.push added) ancestor fuel id = ancestorWalk state.destinations ancestor fuel id := by
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
  rw [frame.destinations, descendant_walk, descendant_walk, Array.size_push]
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
