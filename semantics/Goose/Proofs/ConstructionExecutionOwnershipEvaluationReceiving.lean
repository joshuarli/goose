import Goose.Proofs.ConstructionExecutionOwnershipEvaluationInput
import Goose.Proofs.OwnershipAmbientSuccessorBoundary

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct

def OwnershipChannelReceivingWithinFrames (state : ConstructionState) (outer : OwnershipAmbient) : Channel → Prop
  | .register _ => True
  | .construct incoming => ∀ receiving, destinationCurrent state incoming = .ok receiving →
      OwnershipReceivingWithinSuccessorFrames state outer receiving
  | .completion token =>
      (∀ incoming, state.exitReservations[token]? = some (.waiting incoming) →
        ∀ receiving, destinationCurrent state incoming = .ok receiving →
          OwnershipReceivingWithinSuccessorFrames state outer receiving) ∧
      (∀ role incoming selected snapshot,
        state.exitReservations[token]? = some (.active role incoming selected snapshot) →
        ∀ receiving, destinationCurrent state selected = .ok receiving →
          OwnershipReceivingWithinSuccessorFrames state outer receiving)

def OwnershipFrameReceivingWithinFrames (state : ConstructionState) (outer : OwnershipAmbient) :
    OwnershipAmbientFrame → Prop
  | .callChannels activation _ =>
      ∀ channel ∈ activation.channels, OwnershipChannelReceivingWithinFrames state outer channel
  | .breakTarget target _ =>
      ∀ channel ∈ target.channels, OwnershipChannelReceivingWithinFrames state outer channel
  | .receivingScope capture _ =>
      OwnershipChannelReceivingWithinFrames state outer (.construct capture.incoming)
  | _ => True

def OwnershipCapturedReceivingFrames (state : ConstructionState) : OwnershipAmbient → Prop
  | [] => True
  | frame :: outer => OwnershipFrameReceivingWithinFrames state outer frame ∧
      OwnershipCapturedReceivingFrames state outer

theorem initial_ownershipCapturedReceivingFrames : OwnershipCapturedReceivingFrames .initial [] := True.intro

theorem ownershipCapturedReceivingFrames_suffix (state : ConstructionState) (inner outer : OwnershipAmbient)
    (valid : OwnershipCapturedReceivingFrames state (inner ++ outer)) :
    OwnershipCapturedReceivingFrames state outer := by
  induction inner with
  | nil => exact valid
  | cons frame inner previous => exact previous valid.2

theorem ownershipCapturedReceivingFrames_call (state : ConstructionState) (ambient inner outer : OwnershipAmbient)
    (activation : RuntimeActivation) (carriers : List Construct.Carrier)
    (valid : OwnershipCapturedReceivingFrames state ambient)
    (present : ambient = inner ++ .callChannels activation carriers :: outer) :
    ∀ channel ∈ activation.channels, OwnershipChannelReceivingWithinFrames state outer channel := by
  rw [present] at valid
  exact (ownershipCapturedReceivingFrames_suffix state inner _ valid).1

theorem ownershipCapturedReceivingFrames_break (state : ConstructionState) (ambient inner outer : OwnershipAmbient)
    (target : BreakTarget) (carriers : List Construct.Carrier)
    (valid : OwnershipCapturedReceivingFrames state ambient)
    (present : ambient = inner ++ .breakTarget target carriers :: outer) :
    ∀ channel ∈ target.channels, OwnershipChannelReceivingWithinFrames state outer channel := by
  rw [present] at valid
  exact (ownershipCapturedReceivingFrames_suffix state inner _ valid).1

theorem ownershipCapturedReceivingFrames_call_push (state : ConstructionState) (ambient : OwnershipAmbient)
    (activation : RuntimeActivation) (valid : OwnershipCapturedReceivingFrames state ambient)
    (channels : ∀ channel ∈ activation.channels, OwnershipChannelReceivingWithinFrames state ambient channel) :
    OwnershipCapturedReceivingFrames state (.callChannels activation [] :: ambient) := ⟨channels, valid⟩

theorem ownershipCapturedReceivingFrames_break_push (state : ConstructionState) (ambient : OwnershipAmbient)
    (target : BreakTarget) (valid : OwnershipCapturedReceivingFrames state ambient)
    (channels : ∀ channel ∈ target.channels, OwnershipChannelReceivingWithinFrames state ambient channel) :
    OwnershipCapturedReceivingFrames state (.breakTarget target [] :: ambient) := ⟨channels, valid⟩

theorem ownershipCapturedReceivingFrames_receiving_push (state : ConstructionState) (ambient : OwnershipAmbient)
    (capture : OwnershipReceivingCapture) (valid : OwnershipCapturedReceivingFrames state ambient)
    (channel : OwnershipChannelReceivingWithinFrames state ambient (.construct capture.incoming)) :
    OwnershipCapturedReceivingFrames state (.receivingScope capture [] :: ambient) := ⟨channel, valid⟩

theorem ownershipCapturedReceivingFrames_receiving (state : ConstructionState) (ambient inner outer : OwnershipAmbient)
    (capture : OwnershipReceivingCapture) (carriers : List Construct.Carrier)
    (valid : OwnershipCapturedReceivingFrames state ambient)
    (present : ambient = inner ++ .receivingScope capture carriers :: outer) :
    OwnershipChannelReceivingWithinFrames state outer (.construct capture.incoming) := by
  rw [present] at valid
  exact (ownershipCapturedReceivingFrames_suffix state inner _ valid).1

theorem ownershipCapturedReceivingFrames_returned (state : ConstructionState) (ambient : OwnershipAmbient)
    (carriers : List Construct.Carrier) :
    OwnershipCapturedReceivingFrames state (.returned carriers :: ambient) ↔
      OwnershipCapturedReceivingFrames state ambient := by
  exact ⟨fun valid => valid.2, fun valid => ⟨True.intro, valid⟩⟩

def OwnershipEnvironmentReceiving (state : ConstructionState) (ambient : OwnershipAmbient)
    (environment : RuntimeActivation) : Prop :=
  environment.channels = [] ∨
    ∃ inner captured carriers outer,
      ambient = inner ++ .callChannels captured carriers :: outer ∧
      ownershipActivationChannels captured = ownershipActivationChannels environment ∧
      ∀ channel ∈ captured.channels, OwnershipChannelReceivingWithinFrames state outer channel

theorem ownershipEnvironmentReceiving_empty (state : ConstructionState) (ambient : OwnershipAmbient)
    (environment : RuntimeActivation) (empty : environment.channels = []) :
    OwnershipEnvironmentReceiving state ambient environment := Or.inl empty

theorem ownershipEnvironmentReceiving_activation (state : ExecutionState) (ambient : OwnershipAmbient)
    (environment : RuntimeActivation) (frames : OwnershipRuntimeFrames state ambient)
    (receiving : OwnershipCapturedReceivingFrames state.construction ambient)
    (present : environment ∈ state.activations) :
    OwnershipEnvironmentReceiving state.construction ambient environment := by
  obtain ⟨captured, carriers, member, channels⟩ :=
    ownershipRuntimeFrames_lookup_activation state ambient frames environment present
  obtain ⟨inner, outer, split, _⟩ := List.eq_append_cons_of_mem member
  right
  exact ⟨inner, captured, carriers, outer, split, channels,
    ownershipCapturedReceivingFrames_call state.construction ambient inner outer captured carriers receiving split⟩

end Goose.Proofs.ConstructionExecutionOwnership
