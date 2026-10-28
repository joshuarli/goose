import Goose.Proofs.ConstructionAcceptedEntryActivation
import Goose.Proofs.ConstructionAcceptedGlobalPrefix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
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
    rw [channels] at member
    simp only [List.mem_singleton] at member
    subst channel
    trivial
  have bounds : OwnershipCapturedReceivingBounds state.construction nextAmbient := by
    refine ⟨?_, world.ownership.bounds⟩
    intro channel member
    rw [channels] at member
    simp only [List.mem_singleton] at member
    subst channel
    trivial
  have ownership : OwnershipExecutionContext after nextAmbient :=
    ⟨world.ownership.source, retained, runtime, reservations, receiving, bounds,
      ownershipRuntimeIdentities_activation_push world.ownership.identities activation identifier⟩
  exact acceptedWorld_clockFrame config initialized state after nextAmbient types live world ownership rfl rfl rfl
    (Nat.le_succ _) (Nat.le_refl _)


theorem FutureGlobalsClear.pushActivation {config : EvalConfig} {initialized : Nat} {state : ExecutionState}
    (clear : FutureGlobalsClear config initialized state) (activation : RuntimeActivation) :
    FutureGlobalsClear config initialized
      { state with nextAct := state.nextAct + 1, activations := activation :: state.activations } := clear

theorem ownershipAmbient_call_fresh (state : ExecutionState) (activation : RuntimeActivation) (ambient : OwnershipAmbient)
    (valid : OwnershipExecutionContext state (.callChannels activation [] :: ambient)) :
    OwnershipAmbient.withoutActivation activation.act ambient = ambient := by
  have unique : ((OwnershipAmbient.activations (.callChannels activation [] :: ambient)).map (·.act)).Nodup := by
    rw [← valid.runtime.activations, List.map_map]
    exact valid.identities.activations.1
  have absent : activation.act ∉ (OwnershipAmbient.activations ambient).map (·.act) := by
    have pair : activation.act ∉ (OwnershipAmbient.activations ambient).map (·.act) ∧
        ((OwnershipAmbient.activations ambient).map (·.act)).Nodup := by
      simpa [OwnershipAmbient.activations, OwnershipAmbientFrame.activationChannels, ownershipActivationChannels] using unique
    exact pair.1
  unfold OwnershipAmbient.withoutActivation
  apply List.filter_eq_self.mpr
  intro frame member
  cases frame with
  | callChannels other carriers =>
    have different : other.act ≠ activation.act := by
      intro same
      apply absent
      apply List.mem_map.mpr
      refine ⟨ownershipActivationChannels other, ?_, ?_⟩
      · simp only [OwnershipAmbient.activations, List.mem_filterMap]
        exact ⟨.callChannels other carriers, member, rfl⟩
      · exact same
    simp [different]
  | resultScope _ _ _ | exitChannels _ _ _ | completionChannels _ _ _ => rfl
  | breakTarget _ _ | receivingScope _ _ | returned _ => rfl

theorem ownershipExecutionContext_finishRegisterCall (state : ExecutionState) (activation : RuntimeActivation)
    (ambient : OwnershipAmbient)
    (valid : OwnershipExecutionContext state (.callChannels activation [] :: ambient)) :
    OwnershipExecutionContext
      { state with activations := state.activations.filter (fun current => current.act != activation.act) } ambient := by
  have runtime := ownershipRuntimeFrames_filter_activation state (.callChannels activation [] :: ambient) activation.act valid.runtime
  have reservations := ownershipReservationFrames_pop_released state.construction (.callChannels activation []) ambient
    valid.reservations (by intro token member; simp [OwnershipAmbientFrame.tickets] at member)
  refine ⟨valid.source, ?_, ?_, reservations, valid.receiving.2, valid.bounds.2,
    ownershipRuntimeIdentities_filter_activation valid.identities _⟩
  · refine ⟨valid.retention.structural, ?_, valid.retention.boundaries.2⟩
    simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using valid.retention.anchors
  · have same : OwnershipAmbient.withoutActivation activation.act (.callChannels activation [] :: ambient) = ambient := by
      simpa [OwnershipAmbient.withoutActivation] using ownershipAmbient_call_fresh state activation ambient valid
    rw [same] at runtime
    exact runtime

theorem AcceptedWorld.finishRegisterCall (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (activation : RuntimeActivation) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state (.callChannels activation [] :: ambient) types live regions pending) :
    AcceptedWorld config initialized
      { state with activations := state.activations.filter (fun current => current.act != activation.act) }
      ambient types live regions pending := by
  apply acceptedWorld_clockFrame config initialized state _ ambient types live world
  · exact ownershipExecutionContext_finishRegisterCall state activation ambient world.ownership
  · rfl
  · rfl
  · rfl
  · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem FutureGlobalsClear.finishActivation {config : EvalConfig} {initialized : Nat} {state : ExecutionState}
    (clear : FutureGlobalsClear config initialized state) (activation : RuntimeActivation) :
    FutureGlobalsClear config initialized
      { state with activations := state.activations.filter (fun current => current.act != activation.act) } := clear

theorem finishActivation_register_normal (config : EvalConfig) (initialized : Nat) (activation : RuntimeActivation)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (ty : Ty) (origin : Nat)
    (action : EvalM (List Carrier)) (before after : ExecutionState) (value : Value)
    (channels : activation.channels = [.register ty]) (evaluated : action before = .ok [.register value] after)
    (world : AcceptedWorld config initialized after (.callChannels activation [] :: ambient) types live regions pending)
    (clear : FutureGlobalsClear config initialized after) :
    let final := { after with activations := after.activations.filter (fun current => current.act != activation.act) }
    finishActivation config.layout activation [ty] origin action before = .ok [.register value] final ∧
      AcceptedWorld config initialized final ambient types live regions pending ∧ FutureGlobalsClear config initialized final := by
  refine ⟨?_, world.finishRegisterCall config initialized after activation ambient types live regions pending, clear.finishActivation activation⟩
  simp [finishActivation, evaluated, channels, finishChannels, landCarriersInto, finishChannel,
    List.forIn_cons, List.forIn_nil, bind, pure]

theorem finishActivation_register_stopped (config : EvalConfig) (initialized : Nat) (activation : RuntimeActivation)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (resultTypes : List Ty) (origin : Nat)
    (action : EvalM (List Carrier)) (before after : ExecutionState) (reason : Goose.Core.Stop)
    (evaluated : action before = .stop reason after)
    (world : AcceptedWorld config initialized after (.callChannels activation [] :: ambient) types live regions pending)
    (clear : FutureGlobalsClear config initialized after) :
    finishActivation config.layout activation resultTypes origin action before = .stop reason after ∧
      AcceptedWorld config initialized after (.callChannels activation [] :: ambient) types live regions pending ∧
      FutureGlobalsClear config initialized after := by
  exact ⟨by simp [finishActivation, evaluated], world, clear⟩

#print axioms finishActivation_register_stopped
theorem deliverCarriers_register (fuel : Nat) (config : EvalConfig) (ty : Ty) (value : Value)
    (origin : Nat) (state : ExecutionState) :
    deliverCarriers fuel config.layout [.register ty] [.register value] origin state = .ok [.register value] state := by
  simp [deliverCarriers, bind, pure]

#print axioms finishActivation_register_normal
#print axioms deliverCarriers_register
#print axioms ownershipAmbient_call_fresh
#print axioms ownershipExecutionContext_finishRegisterCall
#print axioms AcceptedWorld.finishRegisterCall
#print axioms FutureGlobalsClear.finishActivation
#print axioms acceptedWorld_pushRegisterActivation
#print axioms FutureGlobalsClear.pushActivation
end Goose.Proofs.ConstructionAcceptedExecution
