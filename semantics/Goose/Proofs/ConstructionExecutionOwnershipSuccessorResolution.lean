import Goose.Proofs.ConstructionExecutionOwnershipSuccessors

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

private theorem destinationCurrentSteps_extension (before after : ConstructionState)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (size : before.destinations.size ≤ after.destinations.size)
    (fuelBefore fuelAfter incoming current : Nat) (fuel : fuelBefore ≤ fuelAfter)
    (resolved : destinationCurrentSteps fuelBefore before incoming = .ok current) :
    destinationCurrentSteps fuelAfter after incoming = .ok current := by
  induction fuelBefore generalizing fuelAfter incoming with
  | zero => simp only [destinationCurrentSteps_zero] at resolved; cases resolved
  | succ fuelBefore previous =>
      cases fuelAfter with
      | zero => omega
      | succ fuelAfter =>
          simp only [destinationCurrentSteps_succ] at resolved ⊢
          split at resolved
          · rename_i inside
            have extended : incoming < after.destinations.size := Nat.lt_of_lt_of_le inside size
            simp only [ite_eq_left extended, successors]
            cases next : before.destinationSuccessors.lookup incoming with
            | none => simpa only [next] using resolved
            | some selected =>
                simp only [next] at resolved ⊢
                split at resolved
                · rename_i ordered
                  simp only [ite_eq_left ordered]
                  exact previous fuelAfter selected (by omega) resolved
                · cases resolved
          · cases resolved

theorem destinationCurrent_extension (before after : ConstructionState)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (size : before.destinations.size ≤ after.destinations.size)
    (incoming current : DestinationId) (resolved : destinationCurrent before incoming = .ok current) :
    destinationCurrent after incoming = .ok current :=
  destinationCurrentSteps_extension before after successors size _ _ incoming current (by omega) resolved

end Goose.Proofs.ConstructionExecutionOwnership
