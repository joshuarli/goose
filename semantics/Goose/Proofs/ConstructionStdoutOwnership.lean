import Goose.Proofs.ConstructionByteStorageContext
import Goose.Proofs.ConstructionExecutionOwnershipSourceTable
import Goose.Proofs.ConstructionExecutionOwnershipSourceState

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem appendStdout_boundaries (state : ExecutionState) (ambient : OwnershipAmbient) (bytes : ByteArray)
    (valid : OwnershipAmbientBoundaries state.construction ambient) :
    OwnershipAmbientBoundaries { state.construction with stdout := state.construction.stdout ++ bytes } ambient := by
  let output := { state.construction with stdout := state.construction.stdout ++ bytes }
  induction ambient with
  | nil => trivial
  | cons head outer ih =>
    refine ⟨?_, ih valid.2⟩
    intro token incoming reserved selected snapshot member ticket resolved retained kept
    have same : destinationCurrent output reserved = destinationCurrent state.construction reserved := by
      rw [destinationCurrent_result, destinationCurrent_result,
        destinationCurrentSteps_same_indexing _ state.construction output rfl rfl]
    change destinationCurrent output reserved = _ at resolved
    rw [same] at resolved
    exact valid.1 token incoming reserved selected snapshot member ticket resolved retained kept

theorem appendStdout_context (state : ExecutionState) (ambient : OwnershipAmbient) (bytes : ByteArray)
    (valid : OwnershipExecutionContext state ambient) :
    OwnershipExecutionContext { state with construction := { state.construction with stdout := state.construction.stdout ++ bytes } } ambient := by
  let output := { state.construction with stdout := state.construction.stdout ++ bytes }
  have source : OwnershipSourceState output := by
    have result := constructionPrimitive_sourceState_of_sourceExtension (appendStdout bytes) (.appendStdout bytes)
      state.construction valid.source (appendStdout_ownership_source bytes state.construction)
    simpa [output, appendStdout, ConstructionM.get, ConstructionM.set, bind, ConstructionResult.finalState] using result
  have extension : OwnershipSourceExtension state.construction output :=
    ownershipSourceExtension_sameRows state.construction output rfl
  have captures := ownershipCapturedReceivingFrames_sourceExtension state.construction output ambient
    valid.source.structural.1.1 valid.source.structural.2.1 source.structural.1.1.1.2.2.2
    extension rfl (Nat.le_refl _) rfl valid.bounds valid.receiving
  refine ⟨source, ⟨source.structural.1, ?_, ?_⟩, ?_, ?_, captures.2, captures.1, ?_⟩
  · intro id row present inactive supported
    have oldSupport := replacementSupported_congr_destinations output state.construction rfl id supported
    exact valid.retention.anchors id row present inactive oldSupport
  · exact appendStdout_boundaries state ambient bytes valid.retention.boundaries
  · exact ⟨valid.runtime.activations, valid.runtime.breaks⟩
  · exact valid.reservations
  · exact ⟨valid.identities.activations, valid.identities.breaks⟩

#print axioms appendStdout_context
end Goose.Proofs.ConstructionAcceptedExecution
