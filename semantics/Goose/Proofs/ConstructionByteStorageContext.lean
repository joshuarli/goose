import Goose.Proofs.ConstructionByteStorageFrame

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem reserveByteStorage_current (state : ExecutionState) (id : Nat) :
    destinationCurrent (reserveByteStorage state).construction id = destinationCurrent state.construction id := by
  rw [destinationCurrent_result, destinationCurrent_result,
    destinationCurrentSteps_same_indexing _ state.construction (reserveByteStorage state).construction rfl rfl]
  rfl

theorem reserveByteStorage_boundaries (state : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipAmbientBoundaries state.construction ambient) :
    OwnershipAmbientBoundaries (reserveByteStorage state).construction ambient := by
  induction ambient with
  | nil => trivial
  | cons head outer ih =>
    refine ⟨?_, ih valid.2⟩
    intro token incoming reserved selected snapshot member ticket resolved retained kept
    rw [reserveByteStorage_current] at resolved
    exact valid.1 token incoming reserved selected snapshot member ticket resolved retained kept

theorem reserveByteStorage_context (state : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipExecutionContext state ambient) :
    OwnershipExecutionContext (reserveByteStorage state) ambient := by
  have source := reserveByteStorage_source state valid.source
  have extension : OwnershipSourceExtension state.construction (reserveByteStorage state).construction :=
    ownershipSourceExtension_sameRows state.construction _ rfl
  have captures := ownershipCapturedReceivingFrames_sourceExtension state.construction
    (reserveByteStorage state).construction ambient valid.source.structural.1.1 valid.source.structural.2.1
    source.structural.1.1.1.2.2.2 extension rfl (Nat.le_refl _) rfl valid.bounds valid.receiving
  refine ⟨source, ⟨source.structural.1, ?_, ?_⟩, ?_, ?_, captures.2, captures.1, ?_⟩
  · intro id row present inactive supported
    have oldSupport := replacementSupported_congr_destinations (reserveByteStorage state).construction state.construction rfl id supported
    exact valid.retention.anchors id row present inactive oldSupport
  · exact reserveByteStorage_boundaries state ambient valid.retention.boundaries
  · exact ⟨valid.runtime.activations, valid.runtime.breaks⟩
  · exact valid.reservations
  · exact ⟨valid.identities.activations, valid.identities.breaks⟩

#print axioms reserveByteStorage_current
#print axioms reserveByteStorage_boundaries
#print axioms reserveByteStorage_context
end Goose.Proofs.ConstructionAcceptedExecution
