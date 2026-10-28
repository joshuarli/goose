import Goose.Proofs.ConstructionExitTargetProtectedRoots
import Goose.Proofs.ConstructionExitCheckpointPostWorld

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks

def recursiveCheckpointRegion : ReceivingRegion := ⟨1, fun _ => False, fun _ => 0, [1]⟩

theorem recursive_checkpoint_protection :
    ReceivingProtection recursiveCheckpointConfig.layout recursiveDirectCheckpoint recursiveCheckpointLive recursiveCheckpointRegion := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨recursiveCheckpointBacking.destination, recursiveCheckpointBacking.present⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro root kept value found
      rcases kept.1 with rfl | rfl <;> cbv at found <;> cases found <;> exact .integer _ _
    · intro root kept stored found
      rcases kept.1 with rfl | rfl <;> cbv at found <;> cases found
    · intro root kept value found stored occurrence
      rcases kept.1 with rfl | rfl <;> cbv at found <;> cases found <;> cases occurrence
  · intro row found
    exact Nat.zero_le _
  · intro row found
    exact Nat.zero_le _
  · simp [recursiveCheckpointRegion]
  · intro id member
    simp only [recursiveCheckpointRegion, List.mem_singleton] at member
    subst id
    cbv
  · intro root live immutable value found stored occurrence id named
    rcases live with rfl | rfl <;> cbv at found <;> cases found <;> cases occurrence

theorem recursive_checkpoint_protected_world :
    AcceptedWorld recursiveCheckpointConfig 0 recursiveDirectCheckpoint recursiveCheckpointAmbient
      recursiveCheckpointTypes recursiveCheckpointLive [recursiveCheckpointRegion] [] := by
  have old := recursive_checkpoint_world
  refine ⟨⟨old.ownership, old.globals, old.globalTypes, old.layouts, old.typeFrontier,
    old.syntheticFrontier, old.heap, old.objectsRegistered, old.ordinalsRegistered, old.backing, ?_, old.carriers⟩, old.globalLive⟩
  intro region member
  simp only [List.mem_singleton] at member
  subst region
  exact recursive_checkpoint_protection

theorem recursive_checkpoint_region_build_conditions :
    (∀ region ∈ [recursiveCheckpointRegion], 1 ∈ region.mutableDestinations) ∧
    (∀ region ∈ [recursiveCheckpointRegion],
      region.limit recursiveCheckpointBacking.destination.storage ≤ recursiveCheckpointBacking.destination.capability.start) ∧
    (∀ root, recursiveCheckpointLive root → ∃ region ∈ [recursiveCheckpointRegion], ¬ region.mutableRoots root) := by
  refine ⟨?_, ?_, ?_⟩
  · intro region member
    simp only [List.mem_singleton] at member
    subst region
    simp [recursiveCheckpointRegion]
  · intro region member
    simp only [List.mem_singleton] at member
    subst region
    exact Nat.zero_le _
  · intro root live
    exact ⟨recursiveCheckpointRegion, by simp, by simp [recursiveCheckpointRegion]⟩

theorem validated_recursive_return_protected_roots :
    validate recursiveDestinations = .ok () ∧
    runModule 32 recursiveCheckpointConfig .initial = .ok () recursiveFullFinal ∧
    ExitReached 32 recursiveCheckpointConfig
      (.statement 4 recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0)) recursiveDirectCheckpoint ∧
    ∃ after : ExecutionState,
      let token := recursiveDirectCheckpoint.construction.exitReservations.size
      let cleaned := { after with construction := { after.construction with
        exitReservations := after.construction.exitReservations.set! token .released } }
      execStmt 4 recursiveCheckpointConfig recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0) recursiveDirectCheckpoint =
        .escape ⟨2, .nonlocal 0⟩ [.completed 1] cleaned ∧
      LandedResultChannels cleaned [.construct 1] [array] [.completed 1] ∧
      ∀ location, recursiveCheckpointLive location.root → ∀ readFuel,
        mapStepState (fun _ => ExecutionState.initial) (readLoc readFuel recursiveCheckpointConfig.layout location cleaned) =
        mapStepState (fun _ => ExecutionState.initial) (readLoc readFuel recursiveCheckpointConfig.layout location recursiveDirectCheckpoint) := by
  have selection : targetActivation recursiveCheckpointConfig 0 recursiveDirectCheckpoint = .ok recursiveCheckpointTarget recursiveDirectCheckpoint := by cbv
  have current : destinationCurrent recursiveDirectCheckpoint.construction 1 = .ok 1 := by cbv
  obtain ⟨after, escaped, landed, _, reads, _⟩ := checked_byte_returnFrom_protected_roots 0 recursiveCheckpointConfig 0
    recursiveCheckpointSource recursiveCheckpointTarget 0 1 [66] 0 recursiveDirectCheckpoint recursiveCheckpointAmbient
    recursiveCheckpointTypes recursiveCheckpointLive [recursiveCheckpointRegion] [] recursiveCheckpointRegion
    recursive_checkpoint_protected_world recursive_checkpoint_ambient_history recursiveCheckpointBacking selection rfl (by simp) rfl rfl rfl rfl rfl rfl current (by decide)
  refine ⟨validated_recursive_direct_return.1, recursive_successful_run_execution.1, recursive_successful_run_reaches_return, after, ?_, ?_, ?_⟩
  · simpa only [array, recursiveCheckpointTarget] using escaped
  · simpa only [array, recursiveCheckpointTarget] using landed
  · intro location live readFuel
    exact reads validated_recursive_direct_return.1 location ⟨live, by simp [recursiveCheckpointRegion]⟩ readFuel

#print axioms recursive_checkpoint_region_build_conditions
#print axioms validated_recursive_return_protected_roots
#print axioms recursive_checkpoint_protected_world

end Goose.Proofs.ConstructionAcceptedExecution
