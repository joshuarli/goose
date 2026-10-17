import Goose.Proofs.ConstructionExecutionProtocolReservationRestore
import Goose.Proofs.ConstructionExecutionProtocolReservationFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private theorem active_before_restored (state : ConstructionState) (token index : ExitReservationId)
    (role : ExitReservationRole) (incoming selected : DestinationId) (snapshot : PendingDestination)
    (present : (state.exitReservations.set! token .restored)[index]? =
      some (.active role incoming selected snapshot)) :
    state.exitReservations[index]? = some (.active role incoming selected snapshot) ∧ token ≠ index := by
  have original : state.exitReservations[index]? = some (.active role incoming selected snapshot) := by
    by_cases same : token = index
    · subst index
      by_cases inside : token < state.exitReservations.size
      · simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, inside] at present
      · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, inside] using present
    · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, same] using present
  refine ⟨original, ?_⟩
  intro same
  subst index
  have inside := (Array.getElem?_eq_some_iff.mp original).choose
  simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, inside] at present

theorem destinationReservationStateValid_restore_ticket (state : ConstructionState) (token : ExitReservationId)
    (valid : DestinationReservationStateValid state) :
    DestinationReservationStateValid { state with exitReservations := state.exitReservations.set! token .restored } := by
  constructor
  · intro index role incoming selected snapshot present
    obtain ⟨original, _⟩ := active_before_restored state token index role incoming selected snapshot present
    obtain ⟨bounds, selectedBound, earlier, phase⟩ := valid.active index role incoming selected snapshot original
    exact ⟨bounds.mono (Nat.le_refl _) (Nat.le_refl _), selectedBound, earlier, phase⟩
  · intro first second role incoming selected snapshot otherRole otherIncoming otherSelected otherSnapshot
      firstPresent secondPresent different selectedDifferent otherDifferent
    exact valid.distinct first second role incoming selected snapshot otherRole otherIncoming otherSelected otherSnapshot
      (active_before_restored state token first role incoming selected snapshot firstPresent).1
      (active_before_restored state token second otherRole otherIncoming otherSelected otherSnapshot secondPresent).1
      different selectedDifferent otherDifferent
  · intro entry member
    exact (valid.resumptions entry member).mono (Nat.le_refl _) (Nat.le_refl _)

theorem destinationReservationStateValid_add_resumption (state : ConstructionState) (id : DestinationId)
    (snapshot : PendingDestination) (bounds : SavedDestinationBounds state id snapshot)
    (valid : DestinationReservationStateValid state) :
    DestinationReservationStateValid { state with destinationResumptions := (id, snapshot) :: state.destinationResumptions } := by
  constructor
  · intro index role incoming selected saved present
    obtain ⟨savedBounds, selectedBound, earlier, phase⟩ := valid.active index role incoming selected saved present
    exact ⟨savedBounds.mono (Nat.le_refl _) (Nat.le_refl _), selectedBound, earlier, phase⟩
  · exact valid.distinct
  · intro entry member
    rcases List.mem_cons.mp member with same | previous
    · subst entry
      exact bounds.mono (Nat.le_refl _) (Nat.le_refl _)
    · exact (valid.resumptions entry previous).mono (Nat.le_refl _) (Nat.le_refl _)

theorem reservationLifecycleInvariant_direct_resumption (state : ConstructionState) (token : ExitReservationId)
    (role : ExitReservationRole) (incoming reserved current : DestinationId) (snapshot : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active role incoming reserved snapshot))
    (earlier : snapshot.capability.id ≤ current) (allocated : current < state.destinations.size)
    (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant { state with
      exitReservations := state.exitReservations.set! token .restored
      destinationResumptions := (current, snapshot) :: state.destinationResumptions } := by
  have bounds := (valid.2.active token role incoming reserved snapshot ticket).1.widen earlier allocated
  have restored := destinationReservationStateValid_restore_ticket state token valid.2
  constructor
  · exact valid.1
  · exact destinationReservationStateValid_add_resumption
      { state with exitReservations := state.exitReservations.set! token .restored } current snapshot
      (bounds.mono (Nat.le_refl _) (Nat.le_refl _)) restored

private theorem snapshotPhase_restore_other (state : ConstructionState) (saved restored : PendingDestination)
    (different : restored.capability.id ≠ saved.capability.id)
    (valid : ReservedSnapshotPhase state saved) :
    ReservedSnapshotPhase { state with destinations := state.destinations.set! restored.capability.id restored } saved := by
  intro current present
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different] at present
  exact valid current present

theorem reservationLifecycleInvariant_restore_ticket (state : ConstructionState) (token : ExitReservationId)
    (role : ExitReservationRole) (incoming selected : DestinationId) (snapshot current : PendingDestination)
    (count expected : Nat)
    (ticket : state.exitReservations[token]? = some (.active role incoming selected snapshot))
    (replaced : snapshot.capability.id ≠ selected)
    (present : state.destinations[snapshot.capability.id]? = some current)
    (exiting : current.progress = .exiting count expected)
    (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant { state with
      destinations := state.destinations.set! snapshot.capability.id snapshot
      exitReservations := state.exitReservations.set! token .restored } := by
  obtain ⟨bounds, selectedBound, earlier, saved⟩ := valid.2.active token role incoming selected snapshot ticket
  obtain ⟨savedProgress, savedPhase⟩ := saved replaced
  constructor
  · have restored := destinationLifecycleInvariant_restore_snapshot state snapshot current count expected
      present exiting bounds savedPhase valid.1
    exact restored
  · constructor
    · intro index otherRole otherIncoming otherSelected otherSnapshot active
      obtain ⟨original, differentTicket⟩ := active_before_restored state token index
        otherRole otherIncoming otherSelected otherSnapshot active
      obtain ⟨otherBounds, otherSelectedBound, otherEarlier, otherSaved⟩ :=
        valid.2.active index otherRole otherIncoming otherSelected otherSnapshot original
      refine ⟨otherBounds.mono (by simp) (Nat.le_refl _), by simpa using otherSelectedBound, otherEarlier, ?_⟩
      intro otherReplaced
      obtain ⟨otherProgress, otherPhase⟩ := otherSaved otherReplaced
      refine ⟨otherProgress, ?_⟩
      have different := valid.2.distinct token index role incoming selected snapshot
        otherRole otherIncoming otherSelected otherSnapshot ticket original differentTicket replaced otherReplaced
      exact snapshotPhase_restore_other state otherSnapshot snapshot different otherPhase
    · intro first second firstOwner firstIncoming firstSelected firstSnapshot secondOwner secondIncoming secondSelected secondSnapshot
        firstPresent secondPresent different firstReplaced secondReplaced
      obtain ⟨firstOriginal, _⟩ := active_before_restored state token first firstOwner firstIncoming firstSelected firstSnapshot firstPresent
      obtain ⟨secondOriginal, _⟩ := active_before_restored state token second secondOwner secondIncoming secondSelected secondSnapshot secondPresent
      exact valid.2.distinct first second firstOwner firstIncoming firstSelected firstSnapshot
        secondOwner secondIncoming secondSelected secondSnapshot firstOriginal secondOriginal different firstReplaced secondReplaced
    · intro entry member
      exact (valid.2.resumptions entry member).mono (by simp) (Nat.le_refl _)

end Goose.Proofs.ConstructionExecutionProtocol
