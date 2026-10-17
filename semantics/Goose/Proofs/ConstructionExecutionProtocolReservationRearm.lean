import Goose.Proofs.ConstructionExecutionOwnershipRearm
import Goose.Proofs.ConstructionExecutionProtocolReservationTickets

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership

private theorem active_before_waiting (state : ConstructionState) (token index : ExitReservationId)
    (incoming : DestinationId) (role : ExitReservationRole) (source selected : DestinationId)
    (snapshot : PendingDestination)
    (present : (state.exitReservations.set! token (.waiting incoming))[index]? =
      some (.active role source selected snapshot)) :
    state.exitReservations[index]? = some (.active role source selected snapshot) := by
  by_cases same : token = index
  · subst index
    by_cases inside : token < state.exitReservations.size
    · simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, inside] at present
    · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, inside] using present
  · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, same] using present

private theorem reservationLifecycleInvariant_waiting (state : ConstructionState)
    (token : ExitReservationId) (incoming : DestinationId) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant {state with exitReservations := state.exitReservations.set! token (.waiting incoming)} := by
  refine ⟨valid.1, ?_⟩
  constructor
  · intro index role source selected snapshot present
    obtain ⟨bounds, allocated, earlier, phase⟩ := valid.2.active index role source selected snapshot
      (active_before_waiting state token index incoming role source selected snapshot present)
    exact ⟨bounds.mono (Nat.le_refl _) (Nat.le_refl _), allocated, earlier, phase⟩
  · intro first second role source selected snapshot otherRole otherSource otherSelected otherSnapshot
      firstPresent secondPresent different firstReplacement secondReplacement
    exact valid.2.distinct first second role source selected snapshot otherRole otherSource otherSelected otherSnapshot
      (active_before_waiting state token first incoming role source selected snapshot firstPresent)
      (active_before_waiting state token second incoming otherRole otherSource otherSelected otherSnapshot secondPresent)
      different firstReplacement secondReplacement
  · intro entry member
    exact (valid.2.resumptions entry member).mono (Nat.le_refl _) (Nat.le_refl _)

theorem rearmExitReservation_lifecycle (borrowed : BorrowedWaitingExitReservation)
    (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (rearmExitReservation borrowed state).finalState := by
  by_cases restored : state.exitReservations[borrowed.token]? = some .restored
  · cases resolved : destinationCurrent state borrowed.incoming with
    | error reason =>
        simpa only [rearmExitReservation_unresolved state borrowed reason restored resolved, ConstructionResult.finalState] using valid
    | ok current =>
        cases present : state.destinations[current]? with
        | none =>
            simpa only [rearmExitReservation_missing state borrowed current restored resolved present, ConstructionResult.finalState] using valid
        | some row =>
            rw [rearmExitReservation_restored state borrowed current row restored resolved present]
            exact reservationLifecycleInvariant_waiting state borrowed.token borrowed.incoming valid
  · simpa only [rearmExitReservation_not_restored state borrowed restored, ConstructionResult.finalState] using valid

theorem rearmExitReservation_destination_capabilities (borrowed : BorrowedWaitingExitReservation) :
    PreservesDestinationCapabilities (rearmExitReservation borrowed) := by
  intro state valid
  have frame := rearmExitReservation_preserves_construction state borrowed
  simpa only [DestinationCapabilitiesIndexed, frame.2.1] using valid

theorem rearmExitReservation_destination_begins (borrowed : BorrowedWaitingExitReservation) :
    PreservesDestinationBegins (rearmExitReservation borrowed) := by
  intro state valid
  have frame := rearmExitReservation_preserves_construction state borrowed
  simpa only [DestinationBegins, frame.2.1, frame.2.2.1] using valid

end Goose.Proofs.ConstructionExecutionProtocol
