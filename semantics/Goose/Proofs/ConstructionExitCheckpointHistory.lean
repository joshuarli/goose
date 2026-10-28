import Goose.Proofs.ConstructionExitCheckpointSource
import Goose.Proofs.ConstructionExitEvaluationHistoryOutcome

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecutionChecks

def recursiveCheckpointAmbient : OwnershipAmbient :=
  recursiveDirectCheckpoint.activations.map (fun activation => .callChannels activation []) ++
    recursiveDirectCheckpoint.breaks.map (fun target => .breakTarget target [])

theorem recursive_checkpoint_timeout_execution :
    runModule 28 ⟨.release, recursiveDestinations⟩ .initial = .stop .timeout recursiveDirectCheckpoint := by
  have observed := recursive_live_activations
  cases result : runModule 28 ⟨.release, recursiveDestinations⟩ .initial with
  | ok value state => simp only [result, timeoutActivations, reduceCtorEq] at observed
  | escape target carriers state => simp only [result, timeoutActivations, reduceCtorEq] at observed
  | jump target kind state => simp only [result, timeoutActivations, reduceCtorEq] at observed
  | stop reason state =>
    cases reason <;> simp only [result, timeoutActivations, reduceCtorEq] at observed
    case timeout => simpa only [recursiveDirectCheckpoint, result, Goose.Proofs.Exit.stepState]

theorem recursive_checkpoint_ambient_history :
    EvaluationHistoryCoverage recursiveDirectCheckpoint recursiveCheckpointAmbient [] := by
  constructor
  · intro frame member
    cbv at member
    cases member with
    | head _ => simp [OwnershipAmbientFrame.tickets]
    | tail _ rest =>
      cases rest with
      | head _ => simp [OwnershipAmbientFrame.tickets]
      | tail _ rest =>
        cases rest with
        | head _ => simp [OwnershipAmbientFrame.tickets]
        | tail _ rest =>
          cases rest with
          | head _ => simp [OwnershipAmbientFrame.tickets]
          | tail _ rest => cases rest
  · intro id retained
    cbv at retained
    cases retained

theorem recursive_checkpoint_runtime_frames :
    OwnershipRuntimeFrames recursiveDirectCheckpoint recursiveCheckpointAmbient := by
  constructor <;> cbv

theorem validated_recursive_checkpoint_history :
    validate recursiveDestinations = .ok () ∧
    runModule 28 ⟨.release, recursiveDestinations⟩ .initial = .stop .timeout recursiveDirectCheckpoint ∧
    OwnershipSourceState recursiveDirectCheckpoint.construction ∧
    OwnershipRuntimeFrames recursiveDirectCheckpoint recursiveCheckpointAmbient ∧
    EvaluationHistoryCoverage recursiveDirectCheckpoint recursiveCheckpointAmbient [] :=
  ⟨validated_recursive_direct_return.1, recursive_checkpoint_timeout_execution, recursive_checkpoint_source,
    recursive_checkpoint_runtime_frames, recursive_checkpoint_ambient_history⟩

#print axioms validated_recursive_checkpoint_history

#print axioms recursive_checkpoint_timeout_execution
#print axioms recursive_checkpoint_ambient_history

end Goose.Proofs.ConstructionAcceptedExecution
