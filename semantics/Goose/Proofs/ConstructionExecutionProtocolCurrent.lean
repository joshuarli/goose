import Goose.Construct.Destination

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem destinationCurrentSteps_bounds (fuel : Nat) (state : ConstructionState)
    (incoming current : DestinationId)
    (resolved : destinationCurrentSteps fuel state incoming = .ok current) :
    incoming ≤ current ∧ current < state.destinations.size := by
  induction fuel generalizing incoming with
  | zero => simp only [destinationCurrentSteps_zero] at resolved; contradiction
  | succ fuel ih =>
      rw [destinationCurrentSteps_succ] at resolved
      split at resolved
      · rename_i inside
        cases successor : state.destinationSuccessors.lookup incoming with
        | none => simp only [successor, Except.ok.injEq] at resolved; subst current; exact ⟨Nat.le_refl _, inside⟩
        | some next =>
            simp only [successor] at resolved
            split at resolved
            · rename_i forward
              obtain ⟨earlier, allocated⟩ := ih next resolved
              exact ⟨Nat.le_trans (Nat.le_of_lt forward) earlier, allocated⟩
            · contradiction
      · contradiction

theorem destinationCurrent_bounds (state : ConstructionState) (incoming current : DestinationId)
    (resolved : destinationCurrent state incoming = .ok current) :
    incoming ≤ current ∧ current < state.destinations.size :=
  destinationCurrentSteps_bounds (state.destinations.size + 1) state incoming current resolved

end Goose.Proofs.ConstructionExecutionProtocol
