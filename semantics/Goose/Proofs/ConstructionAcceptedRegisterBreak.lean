import Goose.Proofs.ConstructionAcceptedRegisterCall
import Goose.Proofs.ConstructionAcceptedCallerContents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem AcceptedWorld.pushRegisterBreak (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (act : Nat) (scope : BreakScope) (ty : Ty)
    (world : AcceptedWorld config initialized state ambient types live regions pending) :
    let target : BreakTarget := ⟨state.nextScope, act, scope, [.register ty]⟩
    AcceptedWorld config initialized
      { state with nextScope := state.nextScope + 1, breaks := target :: state.breaks }
      (.breakTarget target [] :: ambient) types live regions pending := by
  let target : BreakTarget := ⟨state.nextScope, act, scope, [.register ty]⟩
  let after := { state with nextScope := state.nextScope + 1, breaks := target :: state.breaks }
  let nextAmbient := OwnershipAmbientFrame.breakTarget target [] :: ambient
  have retained : OwnershipAmbientInvariant state.construction nextAmbient := by
    refine ⟨world.ownership.retention.structural, ?_, ?_⟩
    · simpa only [nextAmbient, OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers,
        List.nil_append] using world.ownership.retention.anchors
    · refine ⟨?_, world.ownership.retention.boundaries⟩
      intro token incoming reserved selected snapshot member
      cases member
  have runtime : OwnershipRuntimeFrames after nextAmbient :=
    ownershipRuntimeFrames_break_push state ambient act scope [.register ty] world.ownership.runtime
  have reservations : OwnershipReservationFrames state.construction nextAmbient := by
    intro token reservation present needs
    obtain ⟨frame, member, owned⟩ := world.ownership.reservations token reservation present needs
    exact ⟨frame, List.mem_cons_of_mem _ member, owned⟩
  have receiving : OwnershipCapturedReceivingFrames state.construction nextAmbient := by
    apply ownershipCapturedReceivingFrames_break_push state.construction ambient target world.ownership.receiving
    intro channel member
    simp only [target, List.mem_singleton] at member
    subst channel
    trivial
  have bounds : OwnershipCapturedReceivingBounds state.construction nextAmbient := by
    refine ⟨?_, world.ownership.bounds⟩
    intro channel member
    simp only [target, List.mem_singleton] at member
    subst channel
    trivial
  have ownership : OwnershipExecutionContext after nextAmbient :=
    ⟨world.ownership.source, retained, runtime, reservations, receiving, bounds,
      ownershipRuntimeIdentities_break_push world.ownership.identities act scope [.register ty]⟩
  exact acceptedWorld_clockFrame config initialized state after nextAmbient types live world ownership rfl rfl rfl
    (Nat.le_refl _) (Nat.le_succ _)

theorem AcceptedWorld.freshBreakOutside (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types live regions pending) :
    OwnershipAmbient.withoutBreak state.nextScope ambient = ambient := by
  apply List.filter_eq_self.mpr
  intro frame member
  cases frame with
  | breakTarget target carriers =>
    have inAmbient : target ∈ OwnershipAmbient.breaks ambient := by
      exact List.mem_filterMap.mpr ⟨.breakTarget target carriers, member, rfl⟩
    have inState : target ∈ state.breaks := by rw [world.ownership.runtime.breaks]; exact inAmbient
    have bounded := world.ownership.identities.breaks.bounded target inState
    simp only [bne_iff_ne, ne_eq]
    omega
  | _ => rfl

#print axioms AcceptedWorld.freshBreakOutside

theorem ownershipExecutionContext_finishEmptyBreak (state : ExecutionState) (target : BreakTarget)
    (ambient : OwnershipAmbient)
    (valid : OwnershipExecutionContext state (.breakTarget target [] :: ambient))
    (outer : OwnershipAmbient.withoutBreak target.id ambient = ambient) :
    OwnershipExecutionContext
      { state with breaks := state.breaks.filter (fun current => current.id != target.id) } ambient := by
  have runtime := ownershipRuntimeFrames_filter_break state (.breakTarget target [] :: ambient) target.id valid.runtime
  have reservations := ownershipReservationFrames_pop_released state.construction (.breakTarget target []) ambient
    valid.reservations (by intro token member; simp [OwnershipAmbientFrame.tickets] at member)
  refine ⟨valid.source, ?_, ?_, reservations, valid.receiving.2, valid.bounds.2,
    ownershipRuntimeIdentities_filter_break valid.identities _⟩
  · refine ⟨valid.retention.structural, ?_, valid.retention.boundaries.2⟩
    simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using valid.retention.anchors
  · simp only [OwnershipAmbient.withoutBreak, List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at runtime
    rw [OwnershipAmbient.withoutBreak] at outer
    rw [outer] at runtime
    exact runtime

theorem AcceptedWorld.finishEmptyBreak (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (target : BreakTarget) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state (.breakTarget target [] :: ambient) types live regions pending)
    (outer : OwnershipAmbient.withoutBreak target.id ambient = ambient) :
    AcceptedWorld config initialized
      { state with breaks := state.breaks.filter (fun current => current.id != target.id) }
      ambient types live regions pending := by
  apply acceptedWorld_clockFrame config initialized state _ ambient types live world
  · exact ownershipExecutionContext_finishEmptyBreak state target ambient world.ownership outer
  · rfl
  · rfl
  · rfl
  · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem AcceptedFrame.withBreaks {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (breaks : List BreakTarget) :
    AcceptedFrame config accepted frame { state with breaks := breaks } types := by
  apply source.afterFreshActivation <;> simp

theorem AcceptedFrame.pushBreak {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (act : Nat) (scope : BreakScope) (channels : List Channel) :
    let target : BreakTarget := ⟨state.nextScope, act, scope, channels⟩
    AcceptedFrame config accepted frame
      { state with nextScope := state.nextScope + 1, breaks := target :: state.breaks } types := by
  apply source.afterFreshActivation <;> simp

#print axioms AcceptedFrame.withBreaks
#print axioms AcceptedFrame.pushBreak
#print axioms AcceptedWorld.finishEmptyBreak
#print axioms ownershipExecutionContext_finishEmptyBreak
#print axioms AcceptedWorld.pushRegisterBreak
end Goose.Proofs.ConstructionAcceptedExecution
