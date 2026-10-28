import Goose.Proofs.ConstructionAcceptedActivationWorld
import Goose.Proofs.ConstructionAcceptedEntryActivation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem ownershipExecutionContext_finishEmptyCall (state : ExecutionState) (activation : RuntimeActivation)
    (ambient : OwnershipAmbient)
    (valid : OwnershipExecutionContext state (.callChannels activation [] :: ambient))
    (outer : OwnershipAmbient.withoutActivation activation.act ambient = ambient) :
    OwnershipExecutionContext
      { state with activations := state.activations.filter (fun current => current.act != activation.act) } ambient := by
  have runtime := ownershipRuntimeFrames_filter_activation state (.callChannels activation [] :: ambient) activation.act valid.runtime
  have reservations := ownershipReservationFrames_pop_released state.construction (.callChannels activation []) ambient
    valid.reservations (by intro token member; simp [OwnershipAmbientFrame.tickets] at member)
  refine ⟨valid.source, ?_, ?_, reservations, valid.receiving.2, valid.bounds.2,
    ownershipRuntimeIdentities_filter_activation valid.identities _⟩
  · refine ⟨valid.retention.structural, ?_, valid.retention.boundaries.2⟩
    simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using valid.retention.anchors
  · simp only [OwnershipAmbient.withoutActivation, List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at runtime
    change OwnershipAmbient.withoutActivation activation.act ambient = ambient at outer
    rw [OwnershipAmbient.withoutActivation] at outer
    rw [outer] at runtime
    exact runtime

theorem AcceptedWorld.finishEmptyCall (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (activation : RuntimeActivation) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state (.callChannels activation [] :: ambient) types live regions pending)
    (outer : OwnershipAmbient.withoutActivation activation.act ambient = ambient) :
    AcceptedWorld config initialized
      { state with activations := state.activations.filter (fun current => current.act != activation.act) }
      ambient types live regions pending := by
  apply acceptedWorld_clockFrame config initialized state _ ambient types live world
  · exact ownershipExecutionContext_finishEmptyCall state activation ambient world.ownership outer
  · rfl
  · rfl
  · rfl
  · exact Nat.le_refl _
  · exact Nat.le_refl _

#print axioms AcceptedWorld.finishEmptyCall
end Goose.Proofs.ConstructionAcceptedExecution
