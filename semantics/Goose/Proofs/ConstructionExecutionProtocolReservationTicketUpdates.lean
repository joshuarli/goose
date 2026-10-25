import Goose.Proofs.ConstructionExecutionProtocolReservationTickets

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem destinationReservationStateValid_replace_direct (state : ConstructionState)
    (token : ExitReservationId) (role : ExitReservationRole) (incoming selected : DestinationId)
    (snapshot : PendingDestination) (inside : token < state.exitReservations.size)
    (bounds : SavedDestinationBounds state selected snapshot)
    (correct : snapshot.capability.id = selected)
    (valid : DestinationReservationStateValid state) :
    DestinationReservationStateValid {state with
      exitReservations := state.exitReservations.set! token (.active role incoming selected snapshot)} := by
  have lookup (index : ExitReservationId) :
      (state.exitReservations.set! token (.active role incoming selected snapshot))[index]? =
        if index = token then some (.active role incoming selected snapshot) else state.exitReservations[index]? := by
    by_cases same : token = index
    · subst index
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, inside]
    · have different : index ≠ token := Ne.symm same
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, same, different]
  constructor
  · intro index otherRole otherIncoming otherSelected otherSnapshot present
    rw [lookup] at present
    split at present
    · simp only [Option.some.injEq, ExitReservation.active.injEq] at present
      rcases present with ⟨rfl, rfl, rfl, rfl⟩
      refine ⟨?_, bounds.allocated, Nat.le_of_eq correct, ?_⟩
      · simpa only [correct] using bounds.mono (after := {state with exitReservations := state.exitReservations.set! token (.active role incoming selected snapshot)}) (Nat.le_refl _) (Nat.le_refl _)
      · intro different
        exact False.elim (different correct)
    · obtain ⟨otherBounds, allocated, earlier, phase⟩ := valid.active index otherRole otherIncoming otherSelected otherSnapshot present
      exact ⟨otherBounds.mono (Nat.le_refl _) (Nat.le_refl _), allocated, earlier, phase⟩
  · intro first second firstOwner firstIncoming firstSelected firstSnapshot secondOwner secondIncoming secondSelected secondSnapshot
      firstPresent secondPresent different firstReplaced secondReplaced
    rw [lookup] at firstPresent secondPresent
    split at firstPresent
    · simp only [Option.some.injEq, ExitReservation.active.injEq] at firstPresent
      rcases firstPresent with ⟨rfl, rfl, rfl, rfl⟩
      exact False.elim (firstReplaced correct)
    · split at secondPresent
      · simp only [Option.some.injEq, ExitReservation.active.injEq] at secondPresent
        rcases secondPresent with ⟨rfl, rfl, rfl, rfl⟩
        exact False.elim (secondReplaced correct)
      · exact valid.distinct first second firstOwner firstIncoming firstSelected firstSnapshot secondOwner secondIncoming secondSelected secondSnapshot
          firstPresent secondPresent different firstReplaced secondReplaced
  · intro entry member
    exact (valid.resumptions entry member).mono (Nat.le_refl _) (Nat.le_refl _)

end Goose.Proofs.ConstructionExecutionProtocol
