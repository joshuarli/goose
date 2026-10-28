import Goose.Proofs.ConstructionExitCheckpointReservedWorld

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecutionChecks

def recursiveReservedBacking : OpenDestinationBacking recursiveCheckpointConfig.layout
    recursiveReservedState 1 (.varr (.int .u8)) 0 where
  destination := recursiveCheckpointRow
  storage := ⟨⟨#[0, 0, 0, 0]⟩, 0⟩
  present := by cbv
  bytes := by cbv
  logicalType := rfl
  opened := rfl
  element := .int .u8
  elementType := rfl
  fuel := 1
  scan := by cbv
  bounded := by decide
  rollback := by decide

theorem recursive_reserved_current : destinationCurrent recursiveReservedState.construction 1 = .ok 1 := by cbv

theorem recursive_reserved_byte_build :
    ∃ after, buildExpr 1 recursiveCheckpointConfig recursiveCheckpointSource 1 (.bytes array [66] 0) recursiveReservedState = .ok () after := by
  refine ⟨Goose.Proofs.Exit.stepState (buildExpr 1 recursiveCheckpointConfig recursiveCheckpointSource 1 (.bytes array [66] 0) recursiveReservedState), ?_⟩
  cbv

#print axioms recursive_reserved_byte_build

end Goose.Proofs.ConstructionAcceptedExecution
