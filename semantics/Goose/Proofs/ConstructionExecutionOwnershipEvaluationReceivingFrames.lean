import Goose.Proofs.ConstructionExecutionOwnershipEvaluationReceivingSource

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct

def OwnershipFrameReceivingBound (state : ConstructionState) : OwnershipAmbientFrame → Prop
  | .callChannels activation _ => ∀ channel ∈ activation.channels, OwnershipChannelReceivingBound state channel
  | .breakTarget target _ => ∀ channel ∈ target.channels, OwnershipChannelReceivingBound state channel
  | .receivingScope capture _ => OwnershipChannelReceivingBound state (.construct capture.incoming)
  | _ => True

def OwnershipCapturedReceivingBounds (state : ConstructionState) : OwnershipAmbient → Prop
  | [] => True
  | frame :: outer => OwnershipFrameReceivingBound state frame ∧ OwnershipCapturedReceivingBounds state outer

theorem initial_ownershipCapturedReceivingBounds : OwnershipCapturedReceivingBounds .initial [] := True.intro

theorem ownershipCapturedReceivingBounds_receiving_push (state : ConstructionState) (ambient : OwnershipAmbient)
    (capture : OwnershipReceivingCapture) (valid : OwnershipCapturedReceivingBounds state ambient)
    (bound : capture.incoming < state.destinations.size) :
    OwnershipCapturedReceivingBounds state (.receivingScope capture [] :: ambient) := ⟨bound, valid⟩

theorem ownershipCapturedReceivingBounds_receiving (state : ConstructionState) (inner outer : OwnershipAmbient)
    (capture : OwnershipReceivingCapture) (carriers : List Construct.Carrier)
    (valid : OwnershipCapturedReceivingBounds state (inner ++ .receivingScope capture carriers :: outer)) :
    capture.incoming < state.destinations.size := by
  induction inner with
  | nil => exact valid.1
  | cons frame inner previous => exact previous valid.2

theorem ownershipCapturedReceivingBounds_returned (state : ConstructionState) (ambient : OwnershipAmbient)
    (carriers : List Construct.Carrier) :
    OwnershipCapturedReceivingBounds state (.returned carriers :: ambient) ↔
      OwnershipCapturedReceivingBounds state ambient :=
  ⟨fun valid => valid.2, fun valid => ⟨True.intro, valid⟩⟩

theorem ownershipCapturedReceivingFrames_sourceExtension (before after : ConstructionState)
    (ambient : OwnershipAmbient) (lifecycle : Goose.Proofs.ConstructionExecutionProtocol.ReservationLifecycleInvariant before)
    (successors : DestinationSuccessorsValid before)
    (ordered : DestinationOwnersOrdered after)
    (source : OwnershipSourceExtension before after) (map : after.destinationSuccessors = before.destinationSuccessors)
    (size : before.destinations.size ≤ after.destinations.size) (tickets : after.exitReservations = before.exitReservations)
    (bounds : OwnershipCapturedReceivingBounds before ambient) (valid : OwnershipCapturedReceivingFrames before ambient) :
    OwnershipCapturedReceivingBounds after ambient ∧ OwnershipCapturedReceivingFrames after ambient := by
  induction ambient with
  | nil => exact ⟨True.intro, True.intro⟩
  | cons frame outer previous =>
      obtain ⟨outerBounds, outerValid⟩ := previous bounds.2 valid.2
      have headBounds : OwnershipFrameReceivingBound after frame := by
        cases frame <;> try trivial
        case receivingScope capture carriers =>
          exact ownershipChannelReceivingBound_extension before after (.construct capture.incoming) size tickets bounds.1
        all_goals
          intro channel member
          exact ownershipChannelReceivingBound_extension before after channel size tickets (bounds.1 channel member)
      have headValid : OwnershipFrameReceivingWithinFrames after outer frame := by
        cases frame <;> try trivial
        case receivingScope capture carriers =>
          exact ownershipChannelReceivingWithinFrames_source before after outer (.construct capture.incoming)
            lifecycle successors ordered source map size tickets bounds.1 valid.1
        all_goals
          intro channel member
          exact ownershipChannelReceivingWithinFrames_source before after outer channel lifecycle successors ordered
            source map size tickets (bounds.1 channel member) (valid.1 channel member)
      exact ⟨⟨headBounds, outerBounds⟩, ⟨headValid, outerValid⟩⟩

theorem constructionPrimitive_capturedReceiving_of_sourceExtension {α : Type} (action : ConstructionM α)
    (primitive : Goose.Proofs.ConstructionExecutionProtocol.ConstructionPrimitive action)
    (state : ConstructionState) (valid : OwnershipSourceState state) (ambient : OwnershipAmbient)
    (bounds : OwnershipCapturedReceivingBounds state ambient) (receiving : OwnershipCapturedReceivingFrames state ambient)
    (source : OwnershipSourceExtension state (action state).finalState) :
    OwnershipCapturedReceivingBounds (action state).finalState ambient ∧
      OwnershipCapturedReceivingFrames (action state).finalState ambient := by
  have metadata := Goose.Proofs.ConstructionExecutionProtocol.constructionPrimitive_reservation_frame
    action primitive state valid.structural.1.1.1
  have after := constructionPrimitive_sourceState_of_sourceExtension action primitive state valid source
  exact ownershipCapturedReceivingFrames_sourceExtension state _ ambient valid.structural.1.1 valid.structural.2.1
    after.structural.1.1.1.2.2.2 source (constructionPrimitive_successorMap action primitive state)
    metadata.destinations metadata.tickets bounds receiving

end Goose.Proofs.ConstructionExecutionOwnership
