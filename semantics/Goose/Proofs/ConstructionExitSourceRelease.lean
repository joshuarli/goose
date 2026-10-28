import Goose.Proofs.ConstructionExitRetentionRelease
import Goose.Proofs.ConstructionExecutionOwnershipSourceState

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol

theorem fresh_ticket_preimage (state : ConstructionState) (released token incoming selected : Nat)
    (snapshot : PendingDestination)
    (present : (state.exitReservations.set! released .released)[token]? = some (.active .fresh incoming selected snapshot)) :
    state.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
  by_cases same : token = released
  · subst token
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    have releasedTicket : (state.exitReservations.set! released .released)[released]? = some .released := by
      rw [Array.set!_eq_setIfInBounds] at present ⊢
      exact Array.getElem?_setIfInBounds_self_of_lt (by simpa using inside)
    cases present.symm.trans releasedTicket
  · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm same] using present

theorem release_resumption_reservation_roles (state : ConstructionState) (token : Nat)
    (roles : ResumptionReservationRoles state) :
    ResumptionReservationRoles { state with exitReservations := state.exitReservations.set! token .released } := by
  intro key saved stored other incoming reserved snapshot ticket current
  have old := fresh_ticket_preimage state token other incoming reserved snapshot ticket
  have oldCurrent : destinationCurrent state reserved = .ok key := by
    rw [destinationCurrent_congr_tables state
      { state with exitReservations := state.exitReservations.set! token .released } rfl rfl reserved] at current
    exact current
  exact roles key saved stored other incoming reserved snapshot old oldCurrent

theorem release_source_successor_roles (state : ConstructionState) (token : Nat)
    (source : OwnershipSourceState state) :
    let after := { state with exitReservations := state.exitReservations.set! token .released }
    LiveFreshReservationSuccessorRoles after ∧ DestinationSuccessorKeysInactive after ∧
      ResumptionReservationRoles after := by
  refine ⟨live_fresh_roles_after_release state token source.aliases, ?_, release_resumption_reservation_roles state token source.resumptionRoles⟩
  intro id next edge
  exact source.inactiveKeys id next edge

theorem cleanup_source_reservation_roles (state : ExecutionState) (token incoming selected : Nat)
    (snapshot : PendingDestination) (origin : Goose.Core.OriginId) (carriers : List Carrier)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (source : OwnershipSourceState state.construction) :
    ∃ after, Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () after ∧
      ReservationLifecycleInvariant after.construction ∧
      LiveFreshReservationSuccessorRoles after.construction ∧
      DestinationSuccessorKeysInactive after.construction ∧
      ResumptionReservationRoles after.construction := by
  let cleaned := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token .released } }
  have released := releaseExitReservation_active state.construction token .fresh incoming selected snapshot ticket
  have lifecycle := releaseExitReservation_lifecycle state.construction token source.structural.1.1
  rw [released] at lifecycle
  have roles := release_source_successor_roles state.construction token source
  refine ⟨cleaned, ?_, lifecycle, roles⟩
  simp only [Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.forIn_cons, List.forIn_nil,
    liftConstruction, released, bind, pure]
  rfl

#print axioms cleanup_source_reservation_roles
#print axioms release_resumption_reservation_roles
#print axioms release_source_successor_roles

end Goose.Proofs.ConstructionExecutionOwnership
