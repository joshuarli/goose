import Goose.Proofs.ConstructionExitCheckpointHandler

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation

def recursiveOutsideRoot : RootInst := .local 1 1 0

def recursiveOutsideLocation : Loc := ⟨recursiveOutsideRoot, []⟩

theorem recursive_checkpoint_outside_root :
    recursiveDirectCheckpoint.objects.lookup recursiveOutsideRoot = some (.int .i64 1) := by cbv

theorem recursive_checkpoint_outside_backing :
    RootedBackingObservations recursiveCheckpointConfig.layout recursiveDirectCheckpoint
      (fun root => root = recursiveOutsideRoot) (fun _ => 0) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro root equal value found
    subst root
    rw [recursive_checkpoint_outside_root] at found
    cases found
    exact .integer .i64 1
  · intro root equal stored found
    subst root
    rw [recursive_checkpoint_outside_root] at found
    cases found
  · intro root equal value found stored occurrence
    subst root
    rw [recursive_checkpoint_outside_root] at found
    cases found
    cases occurrence

theorem recursive_checkpoint_outside_scopes :
    (Goose.Proofs.Exit.runtimeScopeRoots recursiveHelperActivation 0 recursiveHelperEntered.nextScope).contains recursiveOutsideRoot = false ∧
    (Goose.Proofs.Exit.runtimeScopeRoots recursiveCheckpointTarget 1 recursiveBeforeBranch.nextScope).contains recursiveOutsideRoot = false ∧
    (Goose.Proofs.Exit.runtimeScopeRoots recursiveOuterActivation 0 recursiveOuterEntered.nextScope).contains recursiveOutsideRoot = false := by cbv

theorem recursive_checkpoint_outside_read :
    ∃ final : ExecutionState,
      enterActivation 16 recursiveCheckpointConfig recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody 0 recursiveOuterEntered =
        .ok [.completed 1] final ∧
      mapStepState (fun _ => ExecutionState.initial) (readLoc 1 recursiveCheckpointConfig.layout recursiveOutsideLocation final) =
        .ok (.int .i64 1) .initial := by
  obtain ⟨after, final, matched, _, _, _, reads⟩ := recursive_checkpoint_outer_handler
  have outside : ∀ root, root = recursiveOutsideRoot →
      (Goose.Proofs.Exit.runtimeScopeRoots recursiveHelperActivation 0 recursiveHelperEntered.nextScope).contains root = false ∧
      (Goose.Proofs.Exit.runtimeScopeRoots recursiveCheckpointTarget 1 recursiveBeforeBranch.nextScope).contains root = false ∧
      (Goose.Proofs.Exit.runtimeScopeRoots recursiveOuterActivation 0 recursiveOuterEntered.nextScope).contains root = false := by
    intro root equal
    subst root
    exact recursive_checkpoint_outside_scopes
  have names : ∀ root, root = recursiveOutsideRoot → ∀ value,
      recursiveDirectCheckpoint.objects.lookup root = some value → ∀ stored, StoredOccurrence value stored → stored.destination ≠ some 1 := by
    intro root equal value found stored occurrence
    subst root
    rw [recursive_checkpoint_outside_root] at found
    cases found
    cases occurrence
  have read := reads (fun root => root = recursiveOutsideRoot) (fun _ => 0)
    recursive_checkpoint_outside_backing (by decide) outside names recursiveOutsideLocation rfl 1
  have before : mapStepState (fun _ => ExecutionState.initial)
      (readLoc 1 recursiveCheckpointConfig.layout recursiveOutsideLocation recursiveDirectCheckpoint) = .ok (.int .i64 1) .initial := by cbv
  exact ⟨final, matched, read.trans before⟩

#print axioms recursive_checkpoint_outside_read

end Goose.Proofs.ConstructionAcceptedExecution
