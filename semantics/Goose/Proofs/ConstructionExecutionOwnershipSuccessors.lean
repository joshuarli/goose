import Goose.Construct.Destination

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

def DestinationSuccessorsValid (state : ConstructionState) : Prop :=
  ∀ id next, state.destinationSuccessors.lookup id = some next →
    id < next ∧ next < state.destinations.size

private abbrev currentSteps := destinationCurrentSteps

private theorem currentSteps_zero (state : ConstructionState) (id : DestinationId) :
    currentSteps 0 state id = .error .ownership := rfl

private theorem currentSteps_succ (fuel : Nat) (state : ConstructionState) (id : DestinationId) :
    currentSteps (fuel + 1) state id =
      if id < state.destinations.size then
        match state.destinationSuccessors.lookup id with
        | none => .ok id
        | some next => if id < next then currentSteps fuel state next else .error .ownership
      else .error .destination := rfl

private theorem currentSteps_total (state : ConstructionState) (valid : DestinationSuccessorsValid state)
    (fuel id : Nat) (inside : id < state.destinations.size)
    (sufficient : state.destinations.size ≤ id + fuel) :
    ∃ current, currentSteps fuel state id = .ok current ∧ id ≤ current ∧
      current < state.destinations.size ∧ state.destinationSuccessors.lookup current = none := by
  induction fuel generalizing id with
  | zero => omega
  | succ fuel ih =>
      rw [currentSteps_succ, ite_eq_left inside]
      cases found : state.destinationSuccessors.lookup id with
      | none => exact ⟨id, rfl, Nat.le_refl _, inside, found⟩
      | some next =>
          have bounds := valid id next found
          have orderedNext : id < next := bounds.1
          simp only [ite_eq_left bounds.1]
          obtain ⟨current, result, ordered, inside, terminal⟩ := ih next bounds.2 (by omega)
          exact ⟨current, result, Nat.le_trans (Nat.le_of_lt bounds.1) ordered, inside, terminal⟩

theorem destinationCurrent_total (state : ConstructionState) (valid : DestinationSuccessorsValid state)
    (id : DestinationId) (inside : id < state.destinations.size) :
    ∃ current, destinationCurrent state id = .ok current ∧ id ≤ current ∧
      current < state.destinations.size ∧ state.destinationSuccessors.lookup current = none := by
  have result := currentSteps_total state valid (state.destinations.size + 1) id inside (by omega)
  simpa only [destinationCurrent_result, currentSteps] using result

theorem initial_destination_successors : DestinationSuccessorsValid ConstructionState.initial := by
  intro id next found
  simp [ConstructionState.initial] at found

end Goose.Proofs.ConstructionExecutionOwnership
