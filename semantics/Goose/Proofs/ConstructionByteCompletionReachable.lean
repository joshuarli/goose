import Goose.Proofs.ConstructionAcceptedByteReturnAllFuel
import Goose.Proofs.ConstructionExitCheckpointProtectedWorld

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks

theorem validated_recursive_checkpoint_byte_completion (fuel : Nat) :
    validate recursiveDestinations = .ok () ∧
    ExitReached 32 recursiveCheckpointConfig
      (.statement 4 recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0)) recursiveDirectCheckpoint ∧
    let outcome := withCompletionChannels [.construct 1] 0
      (fun channels => evalProduce fuel recursiveCheckpointConfig recursiveCheckpointSource channels (.bytes array [66] 0))
      recursiveDirectCheckpoint
    ∃ carriers pending,
      AcceptedWorld recursiveCheckpointConfig 0 (Goose.Proofs.Exit.stepState outcome) (.returned carriers :: recursiveCheckpointAmbient)
        recursiveCheckpointTypes recursiveCheckpointLive [recursiveCheckpointRegion] pending ∧
      (match outcome with
      | .ok actual _ => actual = [.completed 1] ∧ carriers = actual ∧ pending = [⟨[.construct 1], [.completed 1]⟩]
      | .stop .. => carriers = [] ∧ pending = []
      | _ => False) := by
  have validated := validated_recursive_return_protected_roots
  refine ⟨validated.1, validated.2.2.1, ?_⟩
  have current : destinationCurrent recursiveDirectCheckpoint.construction 1 = .ok 1 := by cbv
  have noRetained : completedCarrierIds recursiveCheckpointAmbient.retained = [] := by cbv
  exact withCompletion_byteReceiver_allFuel fuel recursiveCheckpointConfig 0 recursiveCheckpointSource 1 [66] 0
    recursiveDirectCheckpoint recursiveCheckpointAmbient recursiveCheckpointTypes recursiveCheckpointLive [recursiveCheckpointRegion]
    recursive_checkpoint_protected_world recursive_checkpoint_ambient_history.1 noRetained recursiveCheckpointBacking
    rfl rfl rfl rfl current (by decide) recursive_checkpoint_region_build_conditions.1
    recursive_checkpoint_region_build_conditions.2.1 recursive_checkpoint_region_build_conditions.2.2

#print axioms validated_recursive_checkpoint_byte_completion
end Goose.Proofs.ConstructionAcceptedExecution
