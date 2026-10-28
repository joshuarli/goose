import Goose.Proofs.ConstructionExitCheckpointReservedBuild

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecutionChecks
open Goose.Proofs.ExitExecution

theorem recursive_reserved_regions_mutable :
    ∀ region ∈ [recursiveCheckpointRegion], 1 ∈ region.mutableDestinations :=
  recursive_checkpoint_region_build_conditions.1

theorem recursive_reserved_regions_cutoff :
    ∀ region ∈ [recursiveCheckpointRegion],
      region.limit recursiveReservedBacking.destination.storage ≤ recursiveReservedBacking.destination.capability.start := by
  intro region member
  simp only [List.mem_singleton] at member
  subst region
  exact Nat.zero_le _

theorem recursive_reserved_regions_covered :
    ∀ root, recursiveCheckpointLive root → ∃ region ∈ [recursiveCheckpointRegion], ¬ region.mutableRoots root :=
  recursive_checkpoint_region_build_conditions.2.2

theorem recursive_reserved_built_world (after : ExecutionState)
    (built : buildExpr 1 recursiveCheckpointConfig recursiveCheckpointSource 1 (.bytes array [66] 0) recursiveReservedState = .ok () after) :
    AcceptedWorld recursiveCheckpointConfig 0 after recursiveReservedAmbient recursiveCheckpointTypes recursiveCheckpointLive [recursiveCheckpointRegion] [] := by
  exact packed_byte_build_accepted_world 0 recursiveCheckpointConfig 0 recursiveCheckpointSource 1 0 [66] 0 recursiveReservedState after
    recursiveReservedAmbient recursiveCheckpointTypes recursiveCheckpointLive [recursiveCheckpointRegion] recursive_reserved_world
    recursiveReservedBacking rfl rfl (by decide) recursive_reserved_current recursive_reserved_regions_mutable
    recursive_reserved_regions_cutoff recursive_reserved_regions_covered built

theorem recursive_reachable_reserved_built_world :
    ExitReached 32 recursiveCheckpointConfig
      (.operands 3 recursiveCheckpointSource [.construct 1] [.bytes array [66] 0]) recursiveReservedState ∧
    AcceptedWorld recursiveCheckpointConfig 0 recursiveReservedState recursiveReservedAmbient recursiveCheckpointTypes recursiveCheckpointLive [recursiveCheckpointRegion] [] ∧
    ∃ after, buildExpr 1 recursiveCheckpointConfig recursiveCheckpointSource 1 (.bytes array [66] 0) recursiveReservedState = .ok () after ∧
      AcceptedWorld recursiveCheckpointConfig 0 after recursiveReservedAmbient recursiveCheckpointTypes recursiveCheckpointLive [recursiveCheckpointRegion] [] := by
  obtain ⟨after, built⟩ := recursive_reserved_byte_build
  exact ⟨recursive_reserved_reached, recursive_reserved_world, after, built, recursive_reserved_built_world after built⟩

#print axioms recursive_reachable_reserved_built_world
#print axioms recursive_reserved_built_world

end Goose.Proofs.ConstructionAcceptedExecution
