import Goose.Proofs.ConstructionExitCheckpointProtectedWorld
import Goose.Proofs.ConstructionExitByteRegions
import Goose.Proofs.ConstructionExitDirectByteSetup

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks

def recursiveReservedState : ExecutionState :=
  { recursiveDirectCheckpoint with construction := { recursiveDirectCheckpoint.construction with
    exitReservations := recursiveDirectCheckpoint.construction.exitReservations.push (.active .fresh 1 1 recursiveCheckpointRow) } }

def recursiveReservedAmbient : OwnershipAmbient :=
  .exitChannels [0] [.construct 1] [] :: recursiveCheckpointAmbient

theorem recursive_reserved_source : OwnershipSourceState recursiveReservedState.construction := by
  have current : destinationCurrent recursiveDirectCheckpoint.construction 1 = .ok 1 := by cbv
  exact direct_fresh_source_state recursiveDirectCheckpoint.construction 1 recursiveCheckpointRow
    recursive_checkpoint_source recursiveCheckpointBacking.present recursiveCheckpointBacking.opened current

theorem recursive_reserved_context : OwnershipExecutionContext recursiveReservedState recursiveReservedAmbient := by
  refine ⟨recursive_reserved_source, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨recursive_reserved_source.structural.1, ?_, ?_⟩
    · intro id row found inactive supported
      have phase := (recursive_checkpoint_receiver_rows id row found).2
      simp [phase, activeProgress] at inactive
    · cbv
      simp [completedCarrierIds]
  · constructor <;> cbv
  · intro token reservation present needed
    cbv at present
    cases token with
    | zero =>
      refine ⟨.exitChannels [0] [.construct 1] [], ?_, ?_⟩ <;> simp [recursiveReservedAmbient, OwnershipAmbientFrame.tickets]
    | succ token => simp at present
  · cbv
    simp [OwnershipChannelReceivingWithinFrames, OwnershipReceivingWithinSuccessorFrames, OwnershipAmbientFrame.tickets]
  · cbv
    simp [OwnershipChannelReceivingBound]
  · refine ⟨recursive_live_activations_fresh, ?_⟩
    cbv
    simp

theorem recursive_reserved_world :
    AcceptedWorld recursiveCheckpointConfig 0 recursiveReservedState recursiveReservedAmbient
      recursiveCheckpointTypes recursiveCheckpointLive [recursiveCheckpointRegion] [] := by
  have old := recursive_checkpoint_protected_world
  refine ⟨⟨recursive_reserved_context, old.globals, old.globalTypes, old.layouts, old.typeFrontier,
    old.syntheticFrontier, old.heap, old.objectsRegistered, old.ordinalsRegistered, ?_, ?_, ?_⟩, old.globalLive⟩
  · constructor
    · intro root live value found
      rcases live with rfl | rfl <;> cbv at found <;> cases found <;> exact .integer _ _
    · intro root live stored found
      rcases live with rfl | rfl <;> cbv at found <;> cases found
  · intro region member
    simp only [List.mem_singleton] at member
    subst region
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨recursiveCheckpointBacking.destination, recursiveCheckpointBacking.present⟩
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro root kept value found
        rcases kept.1 with rfl | rfl <;> cbv at found <;> cases found <;> exact .integer _ _
      · intro root kept stored found
        rcases kept.1 with rfl | rfl <;> cbv at found <;> cases found
      · intro root kept value found stored occurrence
        rcases kept.1 with rfl | rfl <;> cbv at found <;> cases found <;> cases occurrence
    · intro row found; exact Nat.zero_le _
    · intro row found; exact Nat.zero_le _
    · simp [recursiveCheckpointRegion]
    · intro id member
      simp only [recursiveCheckpointRegion, List.mem_singleton] at member
      subst id
      cbv
    · intro root live immutable value found stored occurrence id named
      rcases live with rfl | rfl <;> cbv at found <;> cases found <;> cases occurrence
  · intro frame member
    cases member

theorem recursive_reserved_reached :
    ExitReached 32 recursiveCheckpointConfig
      (.operands 3 recursiveCheckpointSource [.construct 1] [.bytes array [66] 0]) recursiveReservedState := by
  have selection : targetActivation recursiveCheckpointConfig 0 recursiveDirectCheckpoint = .ok recursiveCheckpointTarget recursiveDirectCheckpoint := by cbv
  have current : destinationCurrent recursiveDirectCheckpoint.construction 1 = .ok 1 := by cbv
  have setup := (direct_byte_exit_setup recursiveCheckpointSource recursiveCheckpointTarget [66] 0 recursiveDirectCheckpoint 1 recursiveCheckpointRow rfl recursiveCheckpointBacking.present recursiveCheckpointBacking.opened current).1
  exact .call recursive_successful_run_reaches_return
    (.returnFromOperands 3 recursiveCheckpointSource recursiveCheckpointTarget 0 [.bytes array [66] 0] 0 recursiveDirectCheckpoint recursiveReservedState [.construct 1] selection setup)

#print axioms recursive_reserved_reached

#print axioms recursive_reserved_world

end Goose.Proofs.ConstructionAcceptedExecution
