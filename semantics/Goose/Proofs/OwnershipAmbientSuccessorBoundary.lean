import Goose.Proofs.OwnershipAmbientLandingBoundary
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorPaths

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Core (DestinationId)

def OwnershipLandingAvoidsLiveSuccessors (state : ConstructionState)
    (receiving replacement : DestinationId) : Prop :=
  receiving = replacement ∨
    ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination)
      (node : DestinationId),
      state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      DestinationSuccessorPath state reserved node →
      OwnershipReplacementPath state.destinations receiving node →
      OwnershipReplacementPath state.destinations node replacement → node = receiving

def OwnershipReceivingWithinSuccessorFrames (state : ConstructionState) (outer : OwnershipAmbient)
    (receiving : DestinationId) : Prop :=
  ∀ frame ∈ outer, ∀ token ∈ frame.tickets,
    ∀ (incoming reserved : DestinationId) (snapshot : PendingDestination) (node : DestinationId),
      state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      DestinationSuccessorPath state reserved node →
      OwnershipReplacementPath state.destinations receiving node → node = receiving

theorem ownershipLandingAvoidsLiveSuccessors_direct (state : ConstructionState) (id : DestinationId) :
    OwnershipLandingAvoidsLiveSuccessors state id id := Or.inl rfl

theorem ownershipLandingAvoidsLiveSuccessors_endpoints (state : ConstructionState)
    (receiving replacement : DestinationId)
    (valid : OwnershipLandingAvoidsLiveSuccessors state receiving replacement) :
    OwnershipLandingAvoidsLiveFresh state receiving replacement := by
  rcases valid with same | avoids
  · exact ⟨Or.inl same, Or.inl same⟩
  · constructor
    · right
      intro token incoming reserved current snapshot ticket resolved before after
      exact avoids token incoming reserved snapshot current ticket
        (destinationCurrent_successorPath state reserved current resolved) before after
    · right
      intro token incoming reserved snapshot ticket before after
      exact avoids token incoming reserved snapshot reserved ticket (.refl _) before after

theorem ownershipReceivingWithinSuccessorFrames_endpoints (state : ConstructionState) (outer : OwnershipAmbient)
    (receiving : DestinationId) (valid : OwnershipReceivingWithinSuccessorFrames state outer receiving) :
    OwnershipReceivingWithinFrames state outer receiving := by
  intro frame member token owned incoming reserved snapshot ticket
  constructor
  · exact valid frame member token owned incoming reserved snapshot reserved ticket (.refl _)
  · intro current resolved
    exact valid frame member token owned incoming reserved snapshot current ticket
      (destinationCurrent_successorPath state reserved current resolved)

theorem ownershipReceivingWithinSuccessorFrames_avoids (state : ConstructionState) (outer : OwnershipAmbient)
    (receiving replacement : DestinationId) (owners : OwnershipReservationFrames state outer)
    (boundary : OwnershipReceivingWithinSuccessorFrames state outer receiving) :
    OwnershipLandingAvoidsLiveSuccessors state receiving replacement := by
  right
  intro token incoming reserved snapshot node ticket aliasPath before after
  obtain ⟨frame, member, owned⟩ := owners token _ ticket trivial
  exact boundary frame member token owned incoming reserved snapshot node ticket aliasPath before

theorem ownershipReceivingWithinSuccessorFrames_after_unwind (state : ConstructionState)
    (inner outer : OwnershipAmbient) (capture : OwnershipAmbientFrame)
    (receiving replacement : DestinationId)
    (owners : OwnershipReservationFrames state (inner ++ capture :: outer))
    (released : OwnershipFramesReleased state inner) (noTickets : capture.tickets = [])
    (boundary : OwnershipReceivingWithinSuccessorFrames state outer receiving) :
    OwnershipLandingAvoidsLiveSuccessors state receiving replacement := by
  right
  intro token incoming reserved snapshot node ticket aliasPath before after
  obtain ⟨frame, member, owned⟩ := ownershipReservationFrames_live_fresh_outer state inner outer capture
    owners released noTickets token incoming reserved snapshot ticket
  exact boundary frame member token owned incoming reserved snapshot node ticket aliasPath before

theorem ownershipReceivingWithinSuccessorFrames_initial (outer : OwnershipAmbient) (receiving : DestinationId) :
    OwnershipReceivingWithinSuccessorFrames .initial outer receiving := by
  intro frame member token owned incoming reserved snapshot node ticket
  simp [ConstructionState.initial] at ticket

theorem ownershipReceivingWithinSuccessorFrames_suffix (state : ConstructionState) (inner outer : OwnershipAmbient)
    (receiving : DestinationId) (valid : OwnershipReceivingWithinSuccessorFrames state (inner ++ outer) receiving) :
    OwnershipReceivingWithinSuccessorFrames state outer receiving := by
  intro frame member
  exact valid frame (List.mem_append_right inner member)

theorem ownershipReceivingWithinSuccessorFrames_metadata (before after : ConstructionState)
    (rows : after.destinations = before.destinations)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (tickets : ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (outer : OwnershipAmbient) (receiving : DestinationId)
    (valid : OwnershipReceivingWithinSuccessorFrames before outer receiving) :
    OwnershipReceivingWithinSuccessorFrames after outer receiving := by
  intro frame member token owned incoming reserved snapshot node ticket aliasPath beforePath
  exact valid frame member token owned incoming reserved snapshot node (tickets token incoming reserved snapshot ticket)
    (aliasPath.congr successors.symm) (by simpa only [rows] using beforePath)

#print axioms ownershipLandingAvoidsLiveSuccessors_endpoints
#print axioms ownershipReceivingWithinSuccessorFrames_after_unwind
#print axioms ownershipReceivingWithinSuccessorFrames_avoids
#print axioms ownershipReceivingWithinSuccessorFrames_metadata

end Goose.Proofs.ConstructionExecutionOwnership
