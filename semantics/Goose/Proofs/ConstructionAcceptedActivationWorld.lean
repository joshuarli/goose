import Goose.Proofs.ConstructionAcceptedScopeWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem ownershipExecutionContext_finishEntry (state : ExecutionState) (activation : RuntimeActivation)
    (valid : OwnershipExecutionContext state [.callChannels activation []]) :
    OwnershipExecutionContext
      { state with activations := state.activations.filter (fun current => current.act != activation.act) } [] := by
  have runtime := ownershipRuntimeFrames_filter_activation state [.callChannels activation []] activation.act valid.runtime
  have reservations := ownershipReservationFrames_pop_released state.construction (.callChannels activation []) []
    valid.reservations (by intro token member; simp [OwnershipAmbientFrame.tickets] at member)
  refine ⟨valid.source, ?_, ?_, reservations, trivial, trivial,
    ownershipRuntimeIdentities_filter_activation valid.identities _⟩
  · refine ⟨valid.retention.structural, ?_, trivial⟩
    simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using valid.retention.anchors
  · simpa [OwnershipAmbient.withoutActivation] using runtime

theorem AcceptedWorld.finishEntry (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (activation : RuntimeActivation) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state [.callChannels activation []] types live regions pending) :
    AcceptedWorld config initialized
      { state with activations := state.activations.filter (fun current => current.act != activation.act) }
      [] types live regions pending := by
  apply acceptedWorld_clockFrame config initialized state _ [] types live world
  · exact ownershipExecutionContext_finishEntry state activation world.ownership
  · rfl
  · rfl
  · rfl
  · exact Nat.le_refl _
  · exact Nat.le_refl _

#print axioms ownershipExecutionContext_finishEntry
#print axioms AcceptedWorld.finishEntry
end Goose.Proofs.ConstructionAcceptedExecution
