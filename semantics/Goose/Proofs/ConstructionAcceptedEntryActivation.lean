import Goose.Proofs.ConstructionAcceptedFreshness

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedWorld_pushEmptyActivation (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (activation : RuntimeActivation)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (identifier : activation.act = state.nextAct) (channels : activation.channels = []) :
    AcceptedWorld config initialized
      { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      (.callChannels activation [] :: ambient) types live regions pending := by
  let after := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let nextAmbient := OwnershipAmbientFrame.callChannels activation [] :: ambient
  have retained : OwnershipAmbientInvariant state.construction nextAmbient := by
    refine ⟨world.ownership.retention.structural, ?_, ?_⟩
    · simpa only [nextAmbient, OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers,
        List.nil_append] using world.ownership.retention.anchors
    · refine ⟨?_, world.ownership.retention.boundaries⟩
      intro token incoming reserved selected snapshot member
      cases member
  have runtime : OwnershipRuntimeFrames after nextAmbient := by
    have pushed := ownershipRuntimeFrames_call_push state ambient activation world.ownership.runtime
    exact ⟨pushed.activations, pushed.breaks⟩
  have reservations : OwnershipReservationFrames state.construction nextAmbient := by
    intro token reservation present needs
    obtain ⟨frame, member, owned⟩ := world.ownership.reservations token reservation present needs
    exact ⟨frame, List.mem_cons_of_mem _ member, owned⟩
  have receiving : OwnershipCapturedReceivingFrames state.construction nextAmbient := by
    apply ownershipCapturedReceivingFrames_call_push state.construction ambient activation world.ownership.receiving
    intro channel member
    rw [channels] at member
    cases member
  have bounds : OwnershipCapturedReceivingBounds state.construction nextAmbient := by
    refine ⟨?_, world.ownership.bounds⟩
    intro channel member
    rw [channels] at member
    cases member
  have ownership : OwnershipExecutionContext after nextAmbient :=
    ⟨world.ownership.source, retained, runtime, reservations, receiving, bounds,
      ownershipRuntimeIdentities_activation_push world.ownership.identities activation identifier⟩
  exact acceptedWorld_clockFrame config initialized state after nextAmbient types live world ownership rfl rfl rfl
    (Nat.le_succ _) (Nat.le_refl _)

theorem acceptedWorld_resultScope (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (activation : RuntimeActivation) (scope : Nat)
    (world : AcceptedWorld config initialized state ambient types live regions pending) :
    AcceptedWorld config initialized (ownershipResultScopeState activation scope state) ambient types live regions pending := by
  have ownership : OwnershipExecutionContext (ownershipResultScopeState activation scope state) ambient :=
    ⟨world.ownership.source, world.ownership.retention,
      ownershipRuntimeFrames_resultScope activation scope state ambient world.ownership.runtime,
      world.ownership.reservations, world.ownership.receiving, world.ownership.bounds,
      ownershipRuntimeIdentities_resultScope world.ownership.identities activation scope⟩
  exact acceptedWorld_clockFrame config initialized state (ownershipResultScopeState activation scope state) ambient types live
    world ownership rfl rfl rfl (Nat.le_refl _) (Nat.le_succ _)

#print axioms acceptedWorld_pushEmptyActivation
#print axioms acceptedWorld_resultScope

end Goose.Proofs.ConstructionAcceptedExecution
