import Goose.Proofs.ConstructionExecutionProtocolReservationFrontier
import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupAncestry

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership

theorem exit_frontier_replacement_path (fuel start selected : Nat) (state : ConstructionState)
    (executed : exitFrontierAction fuel start state = .ok selected state) :
    OwnershipReplacementPath state.destinations start selected := by
  induction fuel generalizing start with
  | zero => simp only [exitFrontierAction_zero, ConstructionM.fail] at executed; cases executed
  | succ fuel ih =>
    rw [exitFrontierAction_succ] at executed
    simp only [bind, frontierLookupStep, lookupDestination_result] at executed
    cases found : state.destinations[start]? with
    | none => simp only [found, ConstructionM.fail] at executed; cases executed
    | some row =>
      simp only [found] at executed
      cases progress : row.progress with
      | exiting count next =>
        simp only [progress, frontierLookupStep, lookupDestination_result, bind] at executed
        cases nextFound : state.destinations[next]? with
        | none => simp only [nextFound, ConstructionM.fail] at executed; cases executed
        | some child =>
          simp only [nextFound] at executed
          split at executed
          · simp only [ConstructionM.fail] at executed; cases executed
          · rename_i mismatch
            have use : child.use = .replacement start := by simpa using mismatch
            have suffix := ih next executed
            exact (OwnershipReplacementPath.step next start start child nextFound use (.refl start)).trans suffix
      | «open» count | built count | suspended count child | published count | attached count | abandoned | cancelled | retired =>
        simp only [progress, pure, ConstructionResult.ok.injEq, true_and] at executed
        rcases executed with ⟨rfl, _⟩
        exact .refl _

#print axioms exit_frontier_replacement_path

end Goose.Proofs.ConstructionAcceptedExecution
