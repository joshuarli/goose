import Goose.Proofs.ConstructionAcceptedRegisterCallWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem ownershipReceivingWithin_returned (state : ConstructionState) (ambient : OwnershipAmbient)
    (carriers : List Carrier) (receiving : Nat)
    (valid : OwnershipReceivingWithinSuccessorFrames state ambient receiving) :
    OwnershipReceivingWithinSuccessorFrames state (.returned carriers :: ambient) receiving := by
  intro frame member token owned incoming reserved snapshot node ticket aliases ancestry
  rcases List.mem_cons.mp member with same | old
  · subst frame
    simp [OwnershipAmbientFrame.tickets] at owned
  · exact valid frame old token owned incoming reserved snapshot node ticket aliases ancestry

theorem ownershipChannelWithin_returned (state : ConstructionState) (ambient : OwnershipAmbient)
    (carriers : List Carrier) (channel : Channel)
    (valid : OwnershipChannelReceivingWithinFrames state ambient channel) :
    OwnershipChannelReceivingWithinFrames state (.returned carriers :: ambient) channel := by
  cases channel with
  | register ty => trivial
  | construct id =>
    intro receiving current
    exact ownershipReceivingWithin_returned state ambient carriers receiving (valid receiving current)
  | completion token =>
    constructor
    · intro id ticket receiving current
      exact ownershipReceivingWithin_returned state ambient carriers receiving (valid.1 id ticket receiving current)
    · intro role incoming selected snapshot ticket receiving current
      exact ownershipReceivingWithin_returned state ambient carriers receiving (valid.2 role incoming selected snapshot ticket receiving current)

theorem acceptedWorld_swapReturnedCall (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (activation : RuntimeActivation) (carriers : List Carrier) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state (.returned carriers :: .callChannels activation [] :: ambient)
      types live regions pending) :
    AcceptedWorld config initialized state (.callChannels activation [] :: .returned carriers :: ambient)
      types live regions pending := by
  have retained : OwnershipAmbientInvariant state.construction (.callChannels activation [] :: .returned carriers :: ambient) := by
    refine ⟨world.ownership.retention.structural, ?_, ?_⟩
    · simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using world.ownership.retention.anchors
    · simpa [OwnershipAmbientBoundaries, OwnershipAmbientFrame.tickets, RetainedOutsideTickets] using world.ownership.retention.boundaries
  have runtime : OwnershipRuntimeFrames state (.callChannels activation [] :: .returned carriers :: ambient) := by
    refine ⟨?_, ?_⟩
    · simpa [OwnershipAmbient.activations, OwnershipAmbientFrame.activationChannels, List.filterMap_cons] using world.ownership.runtime.activations
    · simpa [OwnershipAmbient.breaks, OwnershipAmbientFrame.breakChannels, List.filterMap_cons] using world.ownership.runtime.breaks
  have reservations : OwnershipReservationFrames state.construction (.callChannels activation [] :: .returned carriers :: ambient) := by
    intro token reservation present needs
    obtain ⟨frame, member, owned⟩ := world.ownership.reservations token reservation present needs
    simp only [List.mem_cons] at member
    rcases member with same | same | old
    · subst frame
      simp [OwnershipAmbientFrame.tickets] at owned
    · subst frame
      simp [OwnershipAmbientFrame.tickets] at owned
    · exact ⟨frame, by simp [old], owned⟩
  have receiving : OwnershipCapturedReceivingFrames state.construction (.callChannels activation [] :: .returned carriers :: ambient) := by
    refine ⟨?_, ⟨trivial, world.ownership.receiving.2.2⟩⟩
    intro channel member
    exact ownershipChannelWithin_returned state.construction ambient carriers channel (world.ownership.receiving.2.1 channel member)
  have bounds : OwnershipCapturedReceivingBounds state.construction (.callChannels activation [] :: .returned carriers :: ambient) := by
    exact ⟨world.ownership.bounds.2.1, ⟨trivial, world.ownership.bounds.2.2⟩⟩
  have ownership : OwnershipExecutionContext state (.callChannels activation [] :: .returned carriers :: ambient) :=
    ⟨world.ownership.source, retained, runtime, reservations, receiving, bounds, world.ownership.identities⟩
  exact ⟨{ world.toAcceptedWorldCore with ownership := ownership }, world.globalLive⟩

theorem AcceptedWorld.finishReturnedCall (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (activation : RuntimeActivation) (carriers : List Carrier) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state (.returned carriers :: .callChannels activation [] :: ambient)
      types live regions pending) :
    AcceptedWorld config initialized
      { state with activations := state.activations.filter (fun current => current.act != activation.act) }
      (.returned carriers :: ambient) types live regions pending := by
  exact (acceptedWorld_swapReturnedCall config initialized state activation carriers ambient types live regions pending world).finishRegisterCall
    config initialized state activation (.returned carriers :: ambient) types live regions pending

#print axioms acceptedWorld_swapReturnedCall
#print axioms AcceptedWorld.finishReturnedCall
end Goose.Proofs.ConstructionAcceptedExecution
