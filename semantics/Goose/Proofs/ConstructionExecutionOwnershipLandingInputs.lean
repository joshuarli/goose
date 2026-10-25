import Goose.Proofs.ConstructionExecutionOwnershipEvaluationContext
import Goose.Proofs.ConstructionExecutionOwnershipRearm
import Goose.Proofs.OwnershipAmbientFrontiers
import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupAncestry

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

def OwnershipLandingAvoidsFresh (state : ConstructionState) (receiving replacement : DestinationId) : Prop :=
  receiving = replacement ∨
    ∀ (token : ExitReservationId) (incoming reserved current : DestinationId) (snapshot : PendingDestination),
      state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      destinationCurrent state reserved = .ok current →
      OwnershipReplacementPath state.destinations receiving current →
      OwnershipReplacementPath state.destinations current replacement → current = receiving

def OwnershipCarrierLandingInput (state : ConstructionState) : Channel → Construct.Carrier → Prop
  | .construct incoming, .completed replacement =>
      ∀ receiving, destinationCurrent state incoming = .ok receiving →
        OwnershipLandingAvoidsFresh state receiving replacement
  | .completion token, .completed replacement =>
      ∀ role incoming selected snapshot,
        state.exitReservations[token]? = some (.active role incoming selected snapshot) →
        ∀ receiving, destinationCurrent state selected = .ok receiving →
          OwnershipLandingAvoidsFresh state receiving replacement
  | _, _ => True

def OwnershipCarriersLandingInput (state : ConstructionState) (channels : List Channel)
    (carriers : List Construct.Carrier) : Prop :=
  ∀ pair ∈ channels.zip carriers, OwnershipCarrierLandingInput state pair.1 pair.2

theorem ownershipLandingAvoidsFresh_direct (state : ConstructionState) (id : DestinationId) :
    OwnershipLandingAvoidsFresh state id id := Or.inl rfl

theorem ownershipCarrierLandingInput_pending (state : ConstructionState) (channel : Channel)
    (token : ExitReservationId) : OwnershipCarrierLandingInput state channel (.pendingNamed token) := by
  cases channel <;> trivial

theorem ownershipCarrierLandingInput_current (state : ConstructionState) (incoming receiving : DestinationId)
    (resolved : destinationCurrent state incoming = .ok receiving) :
    OwnershipCarrierLandingInput state (.construct incoming) (.completed receiving) := by
  intro current found
  have same : current = receiving := Except.ok.inj (found.symm.trans resolved)
  subst current
  exact ownershipLandingAvoidsFresh_direct state receiving

theorem ownershipCarrierLandingInput_current_completion (state : ConstructionState)
    (token : ExitReservationId) (role : ExitReservationRole) (incoming selected receiving : DestinationId)
    (snapshot : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active role incoming selected snapshot))
    (resolved : destinationCurrent state selected = .ok receiving) :
    OwnershipCarrierLandingInput state (.completion token) (.completed receiving) := by
  intro actualRole actualIncoming actualSelected actualSnapshot actualTicket current found
  have same : ExitReservation.active actualRole actualIncoming actualSelected actualSnapshot =
      .active role incoming selected snapshot := Option.some.inj (actualTicket.symm.trans ticket)
  cases same
  have same : current = receiving := Except.ok.inj (found.symm.trans resolved)
  subst current
  exact ownershipLandingAvoidsFresh_direct state receiving

theorem ownershipLandingAvoidsFresh_no_fresh (state : ConstructionState)
    (noFresh : ∀ (token : ExitReservationId) (incoming selected : DestinationId) (snapshot : PendingDestination),
      state.exitReservations[token]? ≠ some (.active .fresh incoming selected snapshot))
    (receiving replacement : DestinationId) : OwnershipLandingAvoidsFresh state receiving replacement := by
  right
  intro token incoming reserved current snapshot present
  exact False.elim (noFresh token incoming reserved snapshot present)

theorem initial_ownershipCarriersLandingInput (channels : List Channel) (carriers : List Construct.Carrier) :
    OwnershipCarriersLandingInput .initial channels carriers := by
  intro pair member
  rcases pair with ⟨channel, carrier⟩
  cases channel <;> cases carrier <;> simp only [OwnershipCarrierLandingInput]
  · intro receiving resolved
    exact ownershipLandingAvoidsFresh_no_fresh .initial
      (by intro token incoming selected snapshot; simp [ConstructionState.initial]) _ _
  · intro role incoming selected snapshot ticket
    simp [ConstructionState.initial] at ticket


theorem ownershipLandingAvoidsFresh_metadata (before after : ConstructionState)
    (rows : after.destinations = before.destinations)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (tickets : ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (receiving replacement : DestinationId) (valid : OwnershipLandingAvoidsFresh before receiving replacement) :
    OwnershipLandingAvoidsFresh after receiving replacement := by
  rcases valid with direct | avoids
  · exact Or.inl direct
  · right
    intro token incoming reserved current snapshot ticket resolved first second
    apply avoids token incoming reserved current snapshot (tickets token incoming reserved snapshot ticket)
    · simpa only [destinationCurrent_congr_tables before after rows successors] using resolved
    · simpa only [rows] using first
    · simpa only [rows] using second

theorem ownershipCarrierLandingInput_metadata (before after : ConstructionState)
    (rows : after.destinations = before.destinations)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (tickets : ∀ (token : ExitReservationId) (role : ExitReservationRole)
      (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active role incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active role incoming reserved snapshot))
    (channel : Channel) (carrier : Construct.Carrier) (valid : OwnershipCarrierLandingInput before channel carrier) :
    OwnershipCarrierLandingInput after channel carrier := by
  cases channel <;> cases carrier <;> simp only [OwnershipCarrierLandingInput] at valid ⊢
  · intro receiving resolved
    apply ownershipLandingAvoidsFresh_metadata before after rows successors (fun token => tickets token .fresh)
    exact valid receiving (by simpa only [destinationCurrent_congr_tables before after rows successors] using resolved)
  · intro role incoming selected snapshot ticket receiving resolved
    apply ownershipLandingAvoidsFresh_metadata before after rows successors (fun token => tickets token .fresh)
    exact valid role incoming selected snapshot (tickets _ _ _ _ _ ticket) receiving
      (by simpa only [destinationCurrent_congr_tables before after rows successors] using resolved)

theorem ownershipCarriersLandingInput_rearm (receipt : BorrowedWaitingExitReservation) (state : ConstructionState)
    (channels : List Channel) (carriers : List Construct.Carrier)
    (valid : OwnershipCarriersLandingInput state channels carriers) :
    OwnershipCarriersLandingInput (rearmExitReservation receipt state).finalState channels carriers := by
  have frame := rearmExitReservation_preserves_construction state receipt
  intro pair member
  exact ownershipCarrierLandingInput_metadata state _ frame.2.1 frame.2.2.2.2.1
    (rearmExitReservation_active_source receipt state) pair.1 pair.2 (valid pair member)


def OwnershipLandingAvoidsLiveFresh (state : ConstructionState) (receiving replacement : DestinationId) : Prop :=
  OwnershipLandingAvoidsFresh state receiving replacement ∧
    (receiving = replacement ∨
      ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
        state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
        OwnershipReplacementPath state.destinations receiving reserved →
        OwnershipReplacementPath state.destinations reserved replacement → reserved = receiving)

theorem ownershipLandingAvoidsLiveFresh_direct (state : ConstructionState) (id : DestinationId) :
    OwnershipLandingAvoidsLiveFresh state id id := ⟨Or.inl rfl, Or.inl rfl⟩

theorem ownershipLandingAvoidsLiveFresh_no_fresh (state : ConstructionState)
    (noFresh : ∀ (token : ExitReservationId) (incoming selected : DestinationId) (snapshot : PendingDestination),
      state.exitReservations[token]? ≠ some (.active .fresh incoming selected snapshot))
    (receiving replacement : DestinationId) : OwnershipLandingAvoidsLiveFresh state receiving replacement := by
  refine ⟨ownershipLandingAvoidsFresh_no_fresh state noFresh receiving replacement, Or.inr ?_⟩
  intro token incoming reserved snapshot present
  exact False.elim (noFresh token incoming reserved snapshot present)

theorem ownershipLandingAvoidsLiveFresh_metadata (before after : ConstructionState)
    (rows : after.destinations = before.destinations)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (tickets : ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (receiving replacement : DestinationId) (valid : OwnershipLandingAvoidsLiveFresh before receiving replacement) :
    OwnershipLandingAvoidsLiveFresh after receiving replacement := by
  refine ⟨ownershipLandingAvoidsFresh_metadata before after rows successors tickets receiving replacement valid.1, ?_⟩
  rcases valid.2 with direct | avoids
  · exact Or.inl direct
  · right
    intro token incoming reserved snapshot present first second
    exact avoids token incoming reserved snapshot (tickets token incoming reserved snapshot present)
      (by simpa only [rows] using first) (by simpa only [rows] using second)

end Goose.Proofs.ConstructionExecutionOwnership
