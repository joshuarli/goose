import Goose.Proofs.ConstructionAcceptedNestedActivation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedWorld_pushRegisterActivation (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (activation : RuntimeActivation)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (identifier : activation.act = state.nextAct) (ty : Ty) (channels : activation.channels = [.register ty]) :
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
    simp only [channels, List.mem_singleton] at member
    subst channel
    trivial
  have bounds : OwnershipCapturedReceivingBounds state.construction nextAmbient := by
    refine ⟨?_, world.ownership.bounds⟩
    intro channel member
    simp only [channels, List.mem_singleton] at member
    subst channel
    trivial
  have ownership : OwnershipExecutionContext after nextAmbient :=
    ⟨world.ownership.source, retained, runtime, reservations, receiving, bounds,
      ownershipRuntimeIdentities_activation_push world.ownership.identities activation identifier⟩
  exact acceptedWorld_clockFrame config initialized state after nextAmbient types live world ownership rfl rfl rfl
    (Nat.le_succ _) (Nat.le_refl _)


theorem finishChannels_register (layout : LayoutEnv) (ty : Ty) (value : Value) (origin : Nat) (state : ExecutionState) :
    finishChannels layout [.register ty] [ty] [.register value] origin state = .ok () state := by
  simp [finishChannels, landCarriersInto, finishChannel, bind, pure]

theorem deliverCarriers_register (fuel : Nat) (layout : LayoutEnv) (ty : Ty) (value : Value) (origin : Nat) (state : ExecutionState) :
    deliverCarriers fuel layout [.register ty] [.register value] origin state = .ok [.register value] state := by
  simp [deliverCarriers, bind, pure]

theorem finishActivation_register_world (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (activation : RuntimeActivation) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (ty : Ty) (value : Value) (origin : Nat)
    (channels : activation.channels = [.register ty])
    (world : AcceptedWorld config initialized state (.callChannels activation [] :: ambient) types live regions pending)
    (outer : OwnershipAmbient.withoutActivation activation.act ambient = ambient) :
    let after := { state with activations := state.activations.filter (fun current => current.act != activation.act) }
    finishActivation config.layout activation [ty] origin (pure [.register value]) state = .ok [.register value] after ∧
      AcceptedWorld config initialized after ambient types live regions pending := by
  constructor
  · simp [finishActivation, pure, channels, finishChannels_register]
  · exact world.finishEmptyCall config initialized state activation ambient types live regions pending outer

#print axioms finishActivation_register_world
#print axioms acceptedWorld_pushRegisterActivation
#print axioms finishChannels_register
#print axioms deliverCarriers_register
end Goose.Proofs.ConstructionAcceptedExecution
