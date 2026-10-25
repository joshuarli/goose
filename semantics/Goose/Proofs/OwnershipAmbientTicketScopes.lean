import Goose.Proofs.OwnershipAmbientRuntimeFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Core (DestinationId)

def OwnershipReservationNeedsFrame : ExitReservation → Prop
  | .waiting _ | .active .. | .restored => True
  | .released => False

def OwnershipReservationFrames (state : ConstructionState) (ambient : OwnershipAmbient) : Prop :=
  ∀ (token : ExitReservationId) (reservation : ExitReservation),
    state.exitReservations[token]? = some reservation → OwnershipReservationNeedsFrame reservation →
    ∃ frame ∈ ambient, token ∈ frame.tickets

def OwnershipFrameReleased (state : ConstructionState) (frame : OwnershipAmbientFrame) : Prop :=
  ∀ token ∈ frame.tickets, state.exitReservations[token]? = some .released

def OwnershipFramesReleased (state : ConstructionState) (ambient : OwnershipAmbient) : Prop :=
  ∀ frame ∈ ambient, OwnershipFrameReleased state frame

theorem initial_ownershipReservationFrames : OwnershipReservationFrames .initial [] := by
  intro token reservation present
  simp [ConstructionState.initial] at present

theorem ownershipReservationFrames_returned (state : ConstructionState) (ambient : OwnershipAmbient)
    (carriers : List Construct.Carrier) :
    OwnershipReservationFrames state (.returned carriers :: ambient) ↔ OwnershipReservationFrames state ambient := by
  constructor
  · intro valid token reservation present live
    obtain ⟨frame, member, owned⟩ := valid token reservation present live
    rcases List.mem_cons.mp member with same | member
    · subst frame
      simp [OwnershipAmbientFrame.tickets] at owned
    · exact ⟨frame, member, owned⟩
  · intro valid token reservation present live
    obtain ⟨frame, member, owned⟩ := valid token reservation present live
    exact ⟨frame, List.mem_cons_of_mem _ member, owned⟩

theorem ownershipReservationFrames_pop_released (state : ConstructionState) (frame : OwnershipAmbientFrame)
    (outer : OwnershipAmbient) (valid : OwnershipReservationFrames state (frame :: outer))
    (released : OwnershipFrameReleased state frame) : OwnershipReservationFrames state outer := by
  intro token reservation present live
  obtain ⟨owner, member, owned⟩ := valid token reservation present live
  rcases List.mem_cons.mp member with same | member
  · subst owner
    have same : reservation = .released := Option.some.inj (present.symm.trans (released token owned))
    subst reservation
    exact False.elim live
  · exact ⟨owner, member, owned⟩

theorem ownershipReservationFrames_pop_prefix (state : ConstructionState) (inner outer : OwnershipAmbient)
    (valid : OwnershipReservationFrames state (inner ++ outer))
    (released : OwnershipFramesReleased state inner) : OwnershipReservationFrames state outer := by
  intro token reservation present live
  obtain ⟨owner, member, owned⟩ := valid token reservation present live
  rcases List.mem_append.mp member with member | member
  · have same : reservation = .released := Option.some.inj (present.symm.trans (released owner member token owned))
    subst reservation
    exact False.elim live
  · exact ⟨owner, member, owned⟩

theorem ownershipReservationFrames_live_fresh_outer (state : ConstructionState)
    (inner outer : OwnershipAmbient) (frame : OwnershipAmbientFrame)
    (valid : OwnershipReservationFrames state (inner ++ frame :: outer))
    (released : OwnershipFramesReleased state inner) (noTickets : frame.tickets = [])
    (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot)) :
    ∃ owner ∈ outer, token ∈ owner.tickets := by
  have remaining := ownershipReservationFrames_pop_prefix state inner (frame :: outer) valid released
  obtain ⟨owner, member, owned⟩ := remaining token _ ticket trivial
  rcases List.mem_cons.mp member with same | member
  · subst owner
    simp only [noTickets, List.not_mem_nil] at owned
  · exact ⟨owner, member, owned⟩

theorem ownershipReservationFrames_ticket_preimage (before after : ConstructionState)
    (ambient : OwnershipAmbient)
    (preimage : ∀ (token : ExitReservationId) (reservation : ExitReservation),
      after.exitReservations[token]? = some reservation → OwnershipReservationNeedsFrame reservation →
      ∃ original, before.exitReservations[token]? = some original ∧ OwnershipReservationNeedsFrame original)
    (valid : OwnershipReservationFrames before ambient) : OwnershipReservationFrames after ambient := by
  intro token reservation present live
  obtain ⟨original, originalPresent, originalLive⟩ := preimage token reservation present live
  exact valid token original originalPresent originalLive

theorem ownershipReservationFrames_rearm (receipt : BorrowedWaitingExitReservation) (state : ConstructionState)
    (ambient : OwnershipAmbient) (valid : OwnershipReservationFrames state ambient)
    (owner : ∃ frame ∈ ambient, receipt.token ∈ frame.tickets) :
    OwnershipReservationFrames (rearmExitReservation receipt state).finalState ambient := by
  obtain unchanged | waiting := rearmExitReservation_finalState receipt state
  · simpa only [unchanged] using valid
  · rw [waiting]
    intro token reservation present live
    by_cases same : receipt.token = token
    · subst token
      exact owner
    · have original : state.exitReservations[token]? = some reservation := by
        simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using present
      exact valid token reservation original live

theorem releaseExitReservation_released (state : ConstructionState) (token : ExitReservationId)
    (after : ConstructionState) (success : releaseExitReservation token state = .ok () after) :
    after.exitReservations[token]? = some .released := by
  cases present : state.exitReservations[token]? with
  | none => simp [releaseExitReservation_absent_faults state token present] at success
  | some reservation =>
      have inside := (Array.getElem?_eq_some_iff.mp present).1
      cases reservation with
      | released => simp [releaseExitReservation_released_faults state token present] at success
      | waiting incoming =>
          rw [releaseExitReservation_waiting state token incoming present] at success
          cases success
          simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside]
      | restored =>
          rw [releaseExitReservation_restored state token present] at success
          cases success
          simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside]
      | active role incoming selected snapshot =>
          rw [releaseExitReservation_active state token role incoming selected snapshot present] at success
          cases success
          simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside]

#print axioms ownershipReservationFrames_live_fresh_outer
#print axioms ownershipReservationFrames_pop_prefix
#print axioms ownershipReservationFrames_rearm
#print axioms releaseExitReservation_released

end Goose.Proofs.ConstructionExecutionOwnership
