import Goose.Proofs.OwnershipAmbientTicketScopes
import Goose.Proofs.ConstructionExecutionOwnershipLandingInputs

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Core (DestinationId)

def OwnershipReceivingWithinFrames (state : ConstructionState) (outer : OwnershipAmbient)
    (receiving : DestinationId) : Prop :=
  ∀ frame ∈ outer, ∀ token ∈ frame.tickets,
    ∀ (incoming reserved : DestinationId) (snapshot : PendingDestination),
      state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      (OwnershipReplacementPath state.destinations receiving reserved → reserved = receiving) ∧
      (∀ current, destinationCurrent state reserved = .ok current →
        OwnershipReplacementPath state.destinations receiving current → current = receiving)

theorem ownershipReceivingWithinFrames_no_tickets (state : ConstructionState) (outer : OwnershipAmbient)
    (receiving : DestinationId) (empty : ∀ frame ∈ outer, frame.tickets = []) :
    OwnershipReceivingWithinFrames state outer receiving := by
  intro frame member token owned
  simp only [empty frame member, List.not_mem_nil] at owned

theorem ownershipReceivingWithinFrames_initial (outer : OwnershipAmbient) (receiving : DestinationId) :
    OwnershipReceivingWithinFrames .initial outer receiving := by
  intro frame member token owned incoming reserved snapshot ticket
  simp [ConstructionState.initial] at ticket

theorem ownershipReceivingWithinFrames_suffix (state : ConstructionState) (inner outer : OwnershipAmbient)
    (receiving : DestinationId) (valid : OwnershipReceivingWithinFrames state (inner ++ outer) receiving) :
    OwnershipReceivingWithinFrames state outer receiving := by
  intro frame member
  exact valid frame (List.mem_append_right inner member)

theorem ownershipReceivingWithinFrames_avoids (state : ConstructionState) (outer : OwnershipAmbient)
    (receiving replacement : DestinationId) (owners : OwnershipReservationFrames state outer)
    (boundary : OwnershipReceivingWithinFrames state outer receiving) :
    OwnershipLandingAvoidsLiveFresh state receiving replacement := by
  constructor
  · right
    intro token incoming reserved current snapshot ticket resolved before after
    obtain ⟨frame, member, owned⟩ := owners token _ ticket trivial
    exact (boundary frame member token owned incoming reserved snapshot ticket).2 current resolved before
  · right
    intro token incoming reserved snapshot ticket before after
    obtain ⟨frame, member, owned⟩ := owners token _ ticket trivial
    exact (boundary frame member token owned incoming reserved snapshot ticket).1 before

theorem ownershipReceivingWithinFrames_after_unwind (state : ConstructionState)
    (inner outer : OwnershipAmbient) (capture : OwnershipAmbientFrame)
    (receiving replacement : DestinationId)
    (owners : OwnershipReservationFrames state (inner ++ capture :: outer))
    (released : OwnershipFramesReleased state inner) (noTickets : capture.tickets = [])
    (boundary : OwnershipReceivingWithinFrames state outer receiving) :
    OwnershipLandingAvoidsLiveFresh state receiving replacement := by
  apply ownershipReceivingWithinFrames_avoids state outer receiving replacement
  · intro token reservation present live
    have remaining := ownershipReservationFrames_pop_prefix state inner (capture :: outer) owners released
    obtain ⟨frame, member, owned⟩ := remaining token reservation present live
    rcases List.mem_cons.mp member with same | member
    · subst frame
      simp only [noTickets, List.not_mem_nil] at owned
    · exact ⟨frame, member, owned⟩
  · exact boundary

theorem ownershipReceivingWithinFrames_metadata (before after : ConstructionState)
    (rows : after.destinations = before.destinations)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (tickets : ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (outer : OwnershipAmbient) (receiving : DestinationId)
    (valid : OwnershipReceivingWithinFrames before outer receiving) :
    OwnershipReceivingWithinFrames after outer receiving := by
  intro frame member token owned incoming reserved snapshot ticket
  have previous := valid frame member token owned incoming reserved snapshot (tickets token incoming reserved snapshot ticket)
  refine ⟨?_, ?_⟩
  · intro path
    exact previous.1 (by simpa only [rows] using path)
  · intro current resolved path
    exact previous.2 current (by simpa only [destinationCurrent_congr_tables before after rows successors] using resolved)
      (by simpa only [rows] using path)

#print axioms ownershipReceivingWithinFrames_avoids
#print axioms ownershipReceivingWithinFrames_after_unwind
#print axioms ownershipReceivingWithinFrames_metadata

end Goose.Proofs.ConstructionExecutionOwnership
