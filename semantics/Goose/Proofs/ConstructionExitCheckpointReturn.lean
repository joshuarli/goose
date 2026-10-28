import Goose.Proofs.ConstructionExitCheckpointSource
import Goose.Proofs.ConstructionExitDirectReturn

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecutionChecks

def recursiveCheckpointConfig : EvalConfig := ⟨.release, recursiveDestinations⟩

def recursiveCheckpointSource : RuntimeActivation := ⟨2, 3, #[], [(0, 5)], []⟩

def recursiveCheckpointTarget : RuntimeActivation :=
  ⟨1, 2, #[⟨"depth", .int .i64, .immutable, 0, 0⟩,
    ⟨"inner", .varr (.int .u8), .immutable, 2, 0⟩], [(0, 3)], [.construct 1]⟩

def recursiveCheckpointRow : PendingDestination :=
  ⟨⟨1, ⟨.local 1 0 0, []⟩, .varr (.int .u8), .varr (.int .u8), .value, 0, 1⟩,
    .direct 2, .packed, .receiver, .open 0, 4, 0, none, none⟩

def recursiveCheckpointBacking : OpenDestinationBacking recursiveCheckpointConfig.layout
    recursiveDirectCheckpoint 1 (.varr (.int .u8)) 0 where
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

theorem recursive_checkpoint_direct_return :
    ∃ after : ExecutionState,
      let cleaned := { after with construction := { after.construction with
        exitReservations := after.construction.exitReservations.set! 0 .released } }
      execStmt 4 recursiveCheckpointConfig recursiveCheckpointSource (.returnFrom 0 [.bytes (.varr (.int .u8)) [66] 0] 0)
        recursiveDirectCheckpoint = .escape ⟨2, .nonlocal 0⟩ [.completed 1] cleaned ∧
      finishChannels recursiveCheckpointConfig.layout [.construct 1] [.varr (.int .u8)] [.completed 1] 0 cleaned = .ok () cleaned := by
  have selection : targetActivation recursiveCheckpointConfig 0 recursiveDirectCheckpoint = .ok recursiveCheckpointTarget recursiveDirectCheckpoint := by cbv
  have current : destinationCurrent recursiveDirectCheckpoint.construction 1 = .ok 1 := by cbv
  obtain ⟨after, escaped, _, finished, _⟩ := direct_byte_return_cleanup 0 recursiveCheckpointConfig
    recursiveCheckpointSource recursiveCheckpointTarget 0 1 [66] 0 recursiveDirectCheckpoint recursiveCheckpointBacking
    recursive_checkpoint_source selection rfl rfl rfl rfl rfl rfl current (by decide)
  have size : recursiveDirectCheckpoint.construction.exitReservations.size = 0 := by
    rw [recursive_checkpoint_tables.1]
    rfl
  exact ⟨after, by simpa only [size, recursiveCheckpointTarget] using escaped,
    by simpa only [size] using finished⟩

#print axioms recursive_checkpoint_direct_return

end Goose.Proofs.ConstructionAcceptedExecution
