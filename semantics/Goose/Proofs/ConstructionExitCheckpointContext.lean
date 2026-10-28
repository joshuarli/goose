import Goose.Proofs.ConstructionExitCheckpointHistory

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecutionChecks

theorem recursive_checkpoint_execution_context :
    OwnershipExecutionContext recursiveDirectCheckpoint recursiveCheckpointAmbient := by
  refine ⟨recursive_checkpoint_source, ?_, recursive_checkpoint_runtime_frames, ?_, ?_, ?_, ?_⟩
  · refine ⟨recursive_checkpoint_source.structural.1, ?_, ?_⟩
    · intro id row found inactive supported
      have phase := (recursive_checkpoint_receiver_rows id row found).2
      simp [phase, activeProgress] at inactive
    · cbv
      simp
  · intro token reservation present needed
    rw [recursive_checkpoint_tables.1] at present
    simp at present
  · cbv
    simp [OwnershipChannelReceivingWithinFrames, OwnershipReceivingWithinSuccessorFrames, OwnershipAmbientFrame.tickets]
  · cbv
    simp [OwnershipChannelReceivingBound]
  · refine ⟨recursive_live_activations_fresh, ?_⟩
    cbv
    simp

def recursiveCheckpointTypes : RootTypes := fun root =>
  if root = .local 2 3 0 ∨ root = .local 1 1 0 then some (.int .i64) else none

def recursiveCheckpointLive : RootInst → Prop := fun root =>
  root = .local 2 3 0 ∨ root = .local 1 1 0

theorem recursive_checkpoint_world :
    AcceptedWorld ⟨.release, recursiveDestinations⟩ 0 recursiveDirectCheckpoint recursiveCheckpointAmbient
      recursiveCheckpointTypes recursiveCheckpointLive [] [] := by
  refine ⟨⟨recursive_checkpoint_execution_context, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · constructor
    · simp [recursiveDestinations]
    · intro id bound; omega
  · intro id descriptor found
    simp [recursiveDestinations] at found
  · intro root ty declared
    simp only [recursiveCheckpointTypes] at declared
    split at declared
    · cases declared; trivial
    · cases declared
  · intro act scope id ty declared
    simp only [recursiveCheckpointTypes] at declared
    split at declared
    · rename_i root
      rcases root with equal | equal <;> cases equal <;> cbv <;> simp
    · simp at declared
  · intro id ty declared
    simp [recursiveCheckpointTypes] at declared
  · intro root ty value declared found
    have rootCase : root = .local 2 3 0 ∨ root = .local 1 1 0 := by
      by_cases same : root = .local 2 3 0 ∨ root = .local 1 1 0
      · exact same
      · simp [recursiveCheckpointTypes, same] at declared
    rcases rootCase with rfl | rfl <;> cbv at declared found <;> cases declared <;> cases found <;>
      exact ⟨.integer _ _, .integer _ _⟩
  · intro root value found
    cbv at found
    split at found <;> try (cases found)
    all_goals simp_all [List.lookup, recursiveCheckpointTypes]
    all_goals split at found <;> simp_all
  · intro root ordinal found
    cbv at found
    split at found <;> try (cases found)
    all_goals simp_all [List.lookup, recursiveCheckpointTypes]
    all_goals split at found <;> simp_all
  · refine ⟨?_, ?_⟩
    · intro root live value found
      rcases live with rfl | rfl <;> cbv at found <;> cases found <;> exact .integer _ _
    · intro root live stored found
      rcases live with rfl | rfl <;> cbv at found <;> cases found
  · intro region member; cases member
  · intro frame member; cases member
  · intro id bound; omega

#print axioms recursive_checkpoint_world

#print axioms recursive_checkpoint_execution_context

end Goose.Proofs.ConstructionAcceptedExecution
