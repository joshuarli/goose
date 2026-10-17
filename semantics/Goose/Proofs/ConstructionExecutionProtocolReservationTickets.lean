import Goose.Proofs.ConstructionExecutionProtocolReservations

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private theorem active_push_existing (state : ConstructionState) (index : ExitReservationId)
    (role : ExitReservationRole) (incoming selected : DestinationId) (snapshot : PendingDestination)
    (newRole : ExitReservationRole) (newIncoming newSelected : DestinationId) (newSnapshot : PendingDestination)
    (different : index ≠ state.exitReservations.size)
    (present : (state.exitReservations.push (.active newRole newIncoming newSelected newSnapshot))[index]? =
      some (.active role incoming selected snapshot)) :
    state.exitReservations[index]? = some (.active role incoming selected snapshot) := by
  simpa only [Array.getElem?_push, different, ↓reduceIte] using present

theorem destinationReservationStateValid_push (state : ConstructionState) (role : ExitReservationRole)
    (incoming selected : DestinationId) (snapshot : PendingDestination)
    (bounds : SavedDestinationBounds state snapshot.capability.id snapshot)
    (allocated : selected < state.destinations.size) (earlier : snapshot.capability.id ≤ selected)
    (phase : snapshot.capability.id ≠ selected →
      SavedDestinationProgress snapshot.progress ∧ ReservedSnapshotPhase state snapshot)
    (disjoint : snapshot.capability.id ≠ selected →
      ∀ (index : ExitReservationId) (otherRole : ExitReservationRole) (otherIncoming otherSelected : DestinationId)
        (otherSnapshot : PendingDestination),
        state.exitReservations[index]? = some (.active otherRole otherIncoming otherSelected otherSnapshot) →
        otherSnapshot.capability.id ≠ otherSelected → snapshot.capability.id ≠ otherSnapshot.capability.id)
    (valid : DestinationReservationStateValid state) :
    DestinationReservationStateValid { state with
      exitReservations := state.exitReservations.push (.active role incoming selected snapshot) } := by
  constructor
  · intro index otherRole otherIncoming otherSelected otherSnapshot present
    by_cases fresh : index = state.exitReservations.size
    · simp only [Array.getElem?_push, fresh, ↓reduceIte, Option.some.injEq, ExitReservation.active.injEq] at present
      rcases present with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨bounds.mono (Nat.le_refl _) (Nat.le_refl _), allocated, earlier, phase⟩
    · obtain ⟨otherBounds, otherAllocated, otherEarlier, otherPhase⟩ := valid.active index otherRole otherIncoming otherSelected otherSnapshot
        (active_push_existing state index otherRole otherIncoming otherSelected otherSnapshot role incoming selected snapshot fresh present)
      exact ⟨otherBounds.mono (Nat.le_refl _) (Nat.le_refl _), otherAllocated, otherEarlier, otherPhase⟩
  · intro first second firstOwner firstIncoming firstSelected firstSnapshot secondOwner secondIncoming secondSelected secondSnapshot
      firstPresent secondPresent different firstReplaced secondReplaced
    by_cases firstFresh : first = state.exitReservations.size
    · simp only [Array.getElem?_push, firstFresh, ↓reduceIte, Option.some.injEq, ExitReservation.active.injEq] at firstPresent
      rcases firstPresent with ⟨rfl, rfl, rfl, rfl⟩
      have secondOld : second ≠ state.exitReservations.size := by intro equal; exact different (firstFresh.trans equal.symm)
      exact disjoint firstReplaced second secondOwner secondIncoming secondSelected secondSnapshot
        (active_push_existing state second secondOwner secondIncoming secondSelected secondSnapshot role incoming selected snapshot secondOld secondPresent)
        secondReplaced
    · by_cases secondFresh : second = state.exitReservations.size
      · simp only [Array.getElem?_push, secondFresh, ↓reduceIte, Option.some.injEq, ExitReservation.active.injEq] at secondPresent
        rcases secondPresent with ⟨rfl, rfl, rfl, rfl⟩
        exact Ne.symm (disjoint secondReplaced first firstOwner firstIncoming firstSelected firstSnapshot
          (active_push_existing state first firstOwner firstIncoming firstSelected firstSnapshot role incoming selected snapshot firstFresh firstPresent)
          firstReplaced)
      · exact valid.distinct first second firstOwner firstIncoming firstSelected firstSnapshot
          secondOwner secondIncoming secondSelected secondSnapshot
          (active_push_existing state first firstOwner firstIncoming firstSelected firstSnapshot role incoming selected snapshot firstFresh firstPresent)
          (active_push_existing state second secondOwner secondIncoming secondSelected secondSnapshot role incoming selected snapshot secondFresh secondPresent)
          different firstReplaced secondReplaced
  · intro entry member
    exact (valid.resumptions entry member).mono (Nat.le_refl _) (Nat.le_refl _)

theorem reservationLifecycleInvariant_replace_from_push (state : ConstructionState)
    (token : ExitReservationId) (role : ExitReservationRole) (incoming selected : DestinationId)
    (snapshot : PendingDestination)
    (valid : ReservationLifecycleInvariant {state with
      exitReservations := state.exitReservations.push (.active role incoming selected snapshot)}) :
    ReservationLifecycleInvariant {state with
      exitReservations := state.exitReservations.set! token (.active role incoming selected snapshot)} := by
  let ticket := ExitReservation.active role incoming selected snapshot
  have existing (index : ExitReservationId) (otherRole : ExitReservationRole)
      (otherIncoming otherSelected : DestinationId) (otherSnapshot : PendingDestination)
      (present : state.exitReservations[index]? = some (.active otherRole otherIncoming otherSelected otherSnapshot)) :
      (state.exitReservations.push ticket)[index]? = some (.active otherRole otherIncoming otherSelected otherSnapshot) := by
    have inside := (Array.getElem?_eq_some_iff.mp present).choose
    simpa only [Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using present
  have lookup (index : ExitReservationId) :
      (state.exitReservations.set! token ticket)[index]? =
        if token = index ∧ index < state.exitReservations.size then some ticket else state.exitReservations[index]? := by
    by_cases same : token = index
    · subst index
      by_cases inside : token < state.exitReservations.size
      · simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, inside]
      · simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, inside, Array.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt inside)]
    · simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, same]
  have fresh : (state.exitReservations.push ticket)[state.exitReservations.size]? = some ticket := by simp
  constructor
  · exact valid.1
  · constructor
    · intro index otherRole otherIncoming otherSelected otherSnapshot present
      rw [lookup] at present
      split at present
      · simp only [ticket, Option.some.injEq, ExitReservation.active.injEq] at present
        rcases present with ⟨rfl, rfl, rfl, rfl⟩
        obtain ⟨bounds, allocated, earlier, phase⟩ := valid.2.active _ role incoming selected snapshot fresh
        exact ⟨bounds.mono (Nat.le_refl _) (Nat.le_refl _), allocated, earlier, phase⟩
      · obtain ⟨bounds, allocated, earlier, phase⟩ := valid.2.active _ otherRole otherIncoming otherSelected otherSnapshot
          (existing _ _ _ _ _ present)
        exact ⟨bounds.mono (Nat.le_refl _) (Nat.le_refl _), allocated, earlier, phase⟩
    · intro first second firstRole firstIncoming firstSelected firstSnapshot secondRole secondIncoming secondSelected secondSnapshot
        firstPresent secondPresent different firstReplaced secondReplaced
      rw [lookup] at firstPresent secondPresent
      split at firstPresent
      · rename_i firstNew
        simp only [ticket, Option.some.injEq, ExitReservation.active.injEq] at firstPresent
        rcases firstPresent with ⟨rfl, rfl, rfl, rfl⟩
        split at secondPresent
        · rename_i secondNew
          exact False.elim (different (firstNew.1.symm.trans secondNew.1))
        · have secondInside := (Array.getElem?_eq_some_iff.mp secondPresent).choose
          exact valid.2.distinct _ second role incoming selected snapshot secondRole secondIncoming secondSelected secondSnapshot
            fresh (existing _ _ _ _ _ secondPresent) (Ne.symm (Nat.ne_of_lt secondInside)) firstReplaced secondReplaced
      · split at secondPresent
        · simp only [ticket, Option.some.injEq, ExitReservation.active.injEq] at secondPresent
          rcases secondPresent with ⟨rfl, rfl, rfl, rfl⟩
          have firstInside := (Array.getElem?_eq_some_iff.mp firstPresent).choose
          exact valid.2.distinct first _ firstRole firstIncoming firstSelected firstSnapshot role incoming selected snapshot
            (existing _ _ _ _ _ firstPresent) fresh (Nat.ne_of_lt firstInside) firstReplaced secondReplaced
        · exact valid.2.distinct first second firstRole firstIncoming firstSelected firstSnapshot secondRole secondIncoming secondSelected secondSnapshot
            (existing _ _ _ _ _ firstPresent) (existing _ _ _ _ _ secondPresent) different firstReplaced secondReplaced
    · intro entry member
      exact (valid.2.resumptions entry member).mono (Nat.le_refl _) (Nat.le_refl _)

theorem savedDestinationBounds_of_row (state : ConstructionState) (id : DestinationId)
    (snapshot : PendingDestination) (present : state.destinations[id]? = some snapshot)
    (valid : DestinationLifecycleInvariant state) : SavedDestinationBounds state snapshot.capability.id snapshot := by
  have correct := valid.2.1 id snapshot present
  have references := valid.2.2.1 id snapshot present
  refine ⟨Nat.le_refl _, ?_, references.1, references.2, ?_⟩
  · simpa only [correct] using (Array.getElem?_eq_some_iff.mp present).choose
  · have rowOwner := valid.2.2.2 id snapshot present
    cases use : snapshot.use <;> simpa only [use, correct] using rowOwner

theorem reservationLifecycleInvariant_push_active (state : ConstructionState) (role : ExitReservationRole)
    (incoming selected : DestinationId) (snapshot : PendingDestination)
    (bounds : SavedDestinationBounds state snapshot.capability.id snapshot)
    (allocated : selected < state.destinations.size) (earlier : snapshot.capability.id ≤ selected)
    (phase : snapshot.capability.id ≠ selected →
      SavedDestinationProgress snapshot.progress ∧ ReservedSnapshotPhase state snapshot)
    (disjoint : snapshot.capability.id ≠ selected →
      ∀ (index : ExitReservationId) (otherRole : ExitReservationRole) (otherIncoming otherSelected : DestinationId)
        (otherSnapshot : PendingDestination),
        state.exitReservations[index]? = some (.active otherRole otherIncoming otherSelected otherSnapshot) →
        otherSnapshot.capability.id ≠ otherSelected → snapshot.capability.id ≠ otherSnapshot.capability.id)
    (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant { state with
      exitReservations := state.exitReservations.push (.active role incoming selected snapshot) } :=
  ⟨valid.1, destinationReservationStateValid_push state role incoming selected snapshot bounds allocated earlier phase disjoint valid.2⟩

theorem reservationLifecycleInvariant_push_direct (state : ConstructionState) (role : ExitReservationRole)
    (incoming current : DestinationId) (snapshot : PendingDestination)
    (present : state.destinations[current]? = some snapshot) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant { state with
      exitReservations := state.exitReservations.push (.active role incoming current snapshot) } := by
  have correct := valid.1.2.1 current snapshot present
  apply reservationLifecycleInvariant_push_active state role incoming current snapshot
  · exact savedDestinationBounds_of_row state current snapshot present valid.1
  · exact (Array.getElem?_eq_some_iff.mp present).choose
  · exact Nat.le_of_eq correct
  · intro different
    exact False.elim (different correct)
  · intro different
    exact False.elim (different correct)
  · exact valid

theorem reservedSnapshotPhase_ne_mutable (state : ConstructionState) (saved row : PendingDestination)
    (present : state.destinations[row.capability.id]? = some row)
    (mutable : SavedDestinationProgress row.progress) (phase : ReservedSnapshotPhase state saved) :
    saved.capability.id ≠ row.capability.id := by
  intro equal
  have matched := phase row (by simpa only [equal] using present)
  cases progress : row.progress <;> simp_all only [SavedDestinationProgress]

end Goose.Proofs.ConstructionExecutionProtocol
