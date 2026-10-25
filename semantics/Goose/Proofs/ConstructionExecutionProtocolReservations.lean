import Goose.Construct.DestinationTrace

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

structure SavedDestinationBounds (state : ConstructionState) (limit : DestinationId)
    (snapshot : PendingDestination) : Prop where
  capability : snapshot.capability.id ≤ limit
  allocated : limit < state.destinations.size
  writeStorage : snapshot.storage < state.storage.size
  receivingStorage : snapshot.backing.receiverStorage < state.storage.size
  owner : match snapshot.use with
    | .receiver => True
    | .child parent | .replacement parent => parent < limit

def SavedDestinationProgress : DestinationProgress → Prop
  | .open _ | .built _ | .suspended _ _ => True
  | _ => False

def ReservedSnapshotPhase (state : ConstructionState) (snapshot : PendingDestination) : Prop :=
  ∀ current, state.destinations[snapshot.capability.id]? = some current →
    match current.progress with
    | .exiting _ _ => ∀ phase,
        runDestinationTrace snapshot.capability.id .unseen state.events = some phase →
          phase.matchesDestination snapshot
    | .open _ | .built _ | .suspended _ _ => False
    | _ => True

def ActiveExitReservationsValid (state : ConstructionState) : Prop :=
  ∀ (token : ExitReservationId) (role : ExitReservationRole) (incoming selected : DestinationId)
    (snapshot : PendingDestination),
    state.exitReservations[token]? = some (.active role incoming selected snapshot) →
      SavedDestinationBounds state snapshot.capability.id snapshot ∧
      selected < state.destinations.size ∧ snapshot.capability.id ≤ selected ∧
      (snapshot.capability.id ≠ selected →
        SavedDestinationProgress snapshot.progress ∧ ReservedSnapshotPhase state snapshot)

def ReplacementReservationsDistinct (state : ConstructionState) : Prop :=
  ∀ (first second : ExitReservationId) (role : ExitReservationRole) (incoming selected : DestinationId)
    (snapshot : PendingDestination) (otherRole : ExitReservationRole) (otherIncoming otherSelected : DestinationId)
    (otherSnapshot : PendingDestination),
    state.exitReservations[first]? = some (.active role incoming selected snapshot) →
    state.exitReservations[second]? = some (.active otherRole otherIncoming otherSelected otherSnapshot) →
    first ≠ second → snapshot.capability.id ≠ selected →
    otherSnapshot.capability.id ≠ otherSelected → snapshot.capability.id ≠ otherSnapshot.capability.id

def DestinationResumptionsValid (state : ConstructionState) : Prop :=
  ∀ entry ∈ state.destinationResumptions, SavedDestinationBounds state entry.1 entry.2

structure DestinationReservationStateValid (state : ConstructionState) : Prop where
  active : ActiveExitReservationsValid state
  distinct : ReplacementReservationsDistinct state
  resumptions : DestinationResumptionsValid state

theorem initial_destination_reservations : DestinationReservationStateValid ConstructionState.initial := by
  constructor
  · intro token role incoming selected snapshot present
    simp [ConstructionState.initial] at present
  · intro first second role incoming selected snapshot otherRole otherIncoming otherSelected otherSnapshot present
    simp [ConstructionState.initial] at present
  · intro entry member
    simp [ConstructionState.initial] at member

theorem SavedDestinationBounds.mono {before after : ConstructionState} {limit : DestinationId}
    {snapshot : PendingDestination} (valid : SavedDestinationBounds before limit snapshot)
    (destinations : before.destinations.size ≤ after.destinations.size)
    (storage : before.storage.size ≤ after.storage.size) : SavedDestinationBounds after limit snapshot :=
  ⟨valid.capability, Nat.lt_of_lt_of_le valid.allocated destinations,
    Nat.lt_of_lt_of_le valid.writeStorage storage,
    Nat.lt_of_lt_of_le valid.receivingStorage storage, valid.owner⟩

theorem SavedDestinationBounds.widen {state : ConstructionState} {limit next : DestinationId}
    {snapshot : PendingDestination} (valid : SavedDestinationBounds state limit snapshot)
    (earlier : limit ≤ next) (allocated : next < state.destinations.size) :
    SavedDestinationBounds state next snapshot := by
  refine ⟨Nat.le_trans valid.capability earlier, allocated, valid.writeStorage, valid.receivingStorage, ?_⟩
  have owner := valid.owner
  cases use : snapshot.use with
  | receiver => trivial
  | child parent | replacement parent =>
      exact Nat.lt_of_lt_of_le (by simpa only [use] using owner) earlier

private theorem active_before_release (state : ConstructionState) (token index : ExitReservationId)
    (role : ExitReservationRole) (incoming selected : DestinationId) (snapshot : PendingDestination)
    (present : (state.exitReservations.set! token .released)[index]? =
      some (.active role incoming selected snapshot)) :
    state.exitReservations[index]? = some (.active role incoming selected snapshot) := by
  by_cases same : token = index
  · subst index
    by_cases inside : token < state.exitReservations.size
    · simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, inside] at present
    · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, inside] using present
  · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, same] using present

theorem destinationReservationStateValid_release (state : ConstructionState) (token : ExitReservationId)
    (valid : DestinationReservationStateValid state) :
    DestinationReservationStateValid { state with
      exitReservations := state.exitReservations.set! token .released } := by
  constructor
  · intro index role incoming selected snapshot present
    obtain ⟨bounds, selectedBound, earlier, phase⟩ := valid.active index role incoming selected snapshot
      (active_before_release state token index role incoming selected snapshot present)
    exact ⟨bounds.mono (Nat.le_refl _) (Nat.le_refl _), selectedBound, earlier, phase⟩
  · intro first second role incoming selected snapshot otherRole otherIncoming otherSelected otherSnapshot
      firstPresent secondPresent different selectedDifferent otherDifferent
    exact valid.distinct first second role incoming selected snapshot otherRole otherIncoming otherSelected otherSnapshot
      (active_before_release state token first role incoming selected snapshot firstPresent)
      (active_before_release state token second otherRole otherIncoming otherSelected otherSnapshot secondPresent)
      different selectedDifferent otherDifferent
  · intro entry member
    exact (valid.resumptions entry member).mono (Nat.le_refl _) (Nat.le_refl _)

theorem releaseExitReservation_reservations (state : ConstructionState) (token : ExitReservationId)
    (valid : DestinationReservationStateValid state) :
    DestinationReservationStateValid (releaseExitReservation token state).finalState := by
  simp only [releaseExitReservation, ConstructionM.get, bind]
  cases present : state.exitReservations[token]? with
  | none => exact valid
  | some reservation =>
      cases reservation with
      | waiting incoming | active role incoming selected snapshot => exact destinationReservationStateValid_release state token valid
      | restored => exact destinationReservationStateValid_release state token valid
      | released => exact valid

theorem destinationReservationStateValid_storage_frame (state : ConstructionState)
    (storage : Array ReceivingStorage) (size : storage.size = state.storage.size)
    (valid : DestinationReservationStateValid state) :
    DestinationReservationStateValid { state with storage := storage } := by
  constructor
  · intro token role incoming selected snapshot present
    obtain ⟨bounds, selectedBound, earlier, phase⟩ :=
      valid.active token role incoming selected snapshot present
    exact ⟨bounds.mono (Nat.le_refl _) (by simp only [size]; exact Nat.le_refl _), selectedBound, earlier, phase⟩
  · exact valid.distinct
  · intro entry member
    exact (valid.resumptions entry member).mono (Nat.le_refl _) (by simp only [size]; exact Nat.le_refl _)

def ReservationLifecycleInvariant (state : ConstructionState) : Prop :=
  DestinationLifecycleInvariant state ∧ DestinationReservationStateValid state

theorem initial_reservation_lifecycle_invariant :
    ReservationLifecycleInvariant ConstructionState.initial :=
  ⟨initial_destination_lifecycle_invariant, initial_destination_reservations⟩

theorem releaseExitReservation_destination_lifecycle (state : ConstructionState)
    (token : ExitReservationId) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (releaseExitReservation token state).finalState := by
  simp only [releaseExitReservation, ConstructionM.get, bind]
  cases present : state.exitReservations[token]? with
  | none => exact valid
  | some reservation => cases reservation <;> exact valid

theorem reservationLifecycleInvariant_storage_frame (state : ConstructionState)
    (storage : Array ReceivingStorage) (size : storage.size = state.storage.size)
    (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant { state with storage := storage } :=
  ⟨destinationLifecycleInvariant_storage_frame state storage size valid.1,
    destinationReservationStateValid_storage_frame state storage size valid.2⟩

theorem releaseExitReservation_lifecycle (state : ConstructionState) (token : ExitReservationId)
    (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (releaseExitReservation token state).finalState :=
  ⟨releaseExitReservation_destination_lifecycle state token valid.1,
    releaseExitReservation_reservations state token valid.2⟩

end Goose.Proofs.ConstructionExecutionProtocol
