import Goose.Proofs.ConstructionExitCheckpointBuiltWorld

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks

def recursiveBuiltState : ExecutionState :=
  Goose.Proofs.Exit.stepState (buildExpr 1 recursiveCheckpointConfig recursiveCheckpointSource 1 (.bytes array [66] 0) recursiveReservedState)

theorem recursive_built_execution :
    buildExpr 1 recursiveCheckpointConfig recursiveCheckpointSource 1 (.bytes array [66] 0) recursiveReservedState = .ok () recursiveBuiltState := by cbv

theorem recursive_built_produced :
    evalProduce 2 recursiveCheckpointConfig recursiveCheckpointSource [.construct 1] (.bytes array [66] 0) recursiveReservedState =
      .ok [.completed 1] recursiveBuiltState := by cbv

theorem recursive_built_operands :
    evalOperands 3 recursiveCheckpointConfig recursiveCheckpointSource [.construct 1] [.bytes array [66] 0] recursiveReservedState =
      .ok [.completed 1] recursiveBuiltState := by cbv

theorem recursive_built_reached :
    ExitReached 32 recursiveCheckpointConfig (.operands 2 recursiveCheckpointSource [] []) recursiveBuiltState := by
  exact .call recursive_reserved_reached
    (.operandsTail 2 recursiveCheckpointSource (.construct 1) [] (.bytes array [66] 0) [] recursiveReservedState recursiveBuiltState recursiveBuiltState
      [.completed 1] (.completed 1) recursive_built_produced (by cbv))

theorem recursive_built_accepted_world :
    AcceptedWorld recursiveCheckpointConfig 0 recursiveBuiltState recursiveReservedAmbient recursiveCheckpointTypes recursiveCheckpointLive [recursiveCheckpointRegion] [] :=
  recursive_reserved_built_world recursiveBuiltState recursive_built_execution

theorem recursive_built_materialized :
    materializeOwnedCarriers 0 (exitChannelReservationTokens recursiveDirectCheckpoint.construction.exitReservations.size recursiveReservedState)
      [.completed 1] recursiveBuiltState = .ok [.completed 1] recursiveBuiltState := by cbv

theorem recursive_built_cleanup :
    exitChannelCleanupBorrowed 0 (borrowedExitChannelReceipts recursiveCheckpointTarget recursiveDirectCheckpoint)
      (exitChannelReservationTokens recursiveDirectCheckpoint.construction.exitReservations.size recursiveReservedState)
      false [.completed 1] recursiveBuiltState = .ok () recursiveReturnCleaned := by cbv

theorem recursive_reachable_build_cleanup :
    ExitReached 32 recursiveCheckpointConfig (.operands 2 recursiveCheckpointSource [] []) recursiveBuiltState ∧
    AcceptedWorld recursiveCheckpointConfig 0 recursiveBuiltState recursiveReservedAmbient recursiveCheckpointTypes recursiveCheckpointLive [recursiveCheckpointRegion] [] ∧
    evalOperands 3 recursiveCheckpointConfig recursiveCheckpointSource [.construct 1] [.bytes array [66] 0] recursiveReservedState = .ok [.completed 1] recursiveBuiltState ∧
    materializeOwnedCarriers 0 (exitChannelReservationTokens recursiveDirectCheckpoint.construction.exitReservations.size recursiveReservedState)
      [.completed 1] recursiveBuiltState = .ok [.completed 1] recursiveBuiltState ∧
    exitChannelCleanupBorrowed 0 (borrowedExitChannelReceipts recursiveCheckpointTarget recursiveDirectCheckpoint)
      (exitChannelReservationTokens recursiveDirectCheckpoint.construction.exitReservations.size recursiveReservedState)
      false [.completed 1] recursiveBuiltState = .ok () recursiveReturnCleaned ∧
    AcceptedWorld recursiveCheckpointConfig 0 recursiveReturnCleaned recursiveReturnAmbient recursiveCheckpointTypes recursiveCheckpointLive [] recursiveReturnPending :=
  ⟨recursive_built_reached, recursive_built_accepted_world, recursive_built_operands, recursive_built_materialized, recursive_built_cleanup, recursive_return_accepted_world⟩

#print axioms recursive_reachable_build_cleanup

end Goose.Proofs.ConstructionAcceptedExecution
