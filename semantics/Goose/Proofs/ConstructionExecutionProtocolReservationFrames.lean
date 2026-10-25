import Goose.Proofs.ConstructionExecutionProtocolReservations

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

def ReservationStableProgress : DestinationProgress → Prop
  | .open _ | .built _ | .suspended _ _ => False
  | _ => True

structure ReservationRowsFrame (before after : ConstructionState) : Prop where
  preserves : ∀ (index : DestinationId) (initial final : PendingDestination),
    before.destinations[index]? = some initial →
    after.destinations[index]? = some final →
    ReservationStableProgress initial.progress →
    ReservationStableProgress final.progress ∧
      (∀ count selected, final.progress = .exiting count selected →
        ∃ oldCount oldSelected, initial.progress = .exiting oldCount oldSelected ∧
          runDestinationTrace index .unseen after.events =
            runDestinationTrace index .unseen before.events)

structure ReservationMetadataFrame (before after : ConstructionState) : Prop where
  destinations : before.destinations.size ≤ after.destinations.size
  storage : before.storage.size ≤ after.storage.size
  tickets : after.exitReservations = before.exitReservations
  resumptions : after.destinationResumptions = before.destinationResumptions
  rows : ReservationRowsFrame before after

theorem ReservationMetadataFrame.refl (state : ConstructionState) : ReservationMetadataFrame state state := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl, ?_⟩
  constructor
  intro index initial final initialPresent finalPresent stable
  have same : initial = final := Option.some.inj (initialPresent.symm.trans finalPresent)
  subst final
  exact ⟨stable, fun count selected progress => ⟨count, selected, progress, rfl⟩⟩

theorem ReservationMetadataFrame.trans {before middle after : ConstructionState}
    (first : ReservationMetadataFrame before middle) (second : ReservationMetadataFrame middle after) :
    ReservationMetadataFrame before after := by
  refine ⟨Nat.le_trans first.destinations second.destinations, Nat.le_trans first.storage second.storage,
    second.tickets.trans first.tickets, second.resumptions.trans first.resumptions, ?_⟩
  constructor
  intro index initial final initialPresent finalPresent stable
  have inside := (Array.getElem?_eq_some_iff.mp initialPresent).choose
  have middleInside : index < middle.destinations.size := Nat.lt_of_lt_of_le inside first.destinations
  let interim := middle.destinations[index]
  have interimPresent : middle.destinations[index]? = some interim := Array.getElem?_eq_getElem middleInside
  obtain ⟨interimStable, interimExiting⟩ := first.rows.preserves index initial interim initialPresent interimPresent stable
  obtain ⟨finalStable, finalExiting⟩ := second.rows.preserves index interim final interimPresent finalPresent interimStable
  refine ⟨finalStable, ?_⟩
  intro count selected progress
  obtain ⟨middleCount, middleSelected, middleProgress, secondTrace⟩ := finalExiting count selected progress
  obtain ⟨oldCount, oldSelected, oldProgress, firstTrace⟩ := interimExiting middleCount middleSelected middleProgress
  exact ⟨oldCount, oldSelected, oldProgress, secondTrace.trans firstTrace⟩

theorem reservationMetadataFrame_same_rows (before after : ConstructionState)
    (destinations : after.destinations = before.destinations) (events : after.events = before.events)
    (tickets : after.exitReservations = before.exitReservations)
    (resumptions : after.destinationResumptions = before.destinationResumptions)
    (storage : before.storage.size ≤ after.storage.size) : ReservationMetadataFrame before after := by
  refine ⟨by simp only [destinations]; exact Nat.le_refl _, storage, tickets, resumptions, ?_⟩
  constructor
  intro index initial final initialPresent finalPresent stable
  rw [destinations] at finalPresent
  have same : initial = final := Option.some.inj (initialPresent.symm.trans finalPresent)
  subst final
  exact ⟨stable, fun count selected progress => ⟨count, selected, progress, by rw [events]⟩⟩

theorem reserveStorage_reservation_frame (bytes : ByteArray) (count : Nat) (state : ConstructionState) :
    ReservationMetadataFrame state (reserveStorage bytes count state).finalState := by
  apply reservationMetadataFrame_same_rows <;> first | rfl | simp [reserveStorage, ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.finalState]

theorem appendStdout_reservation_frame (bytes : ByteArray) (state : ConstructionState) :
    ReservationMetadataFrame state (appendStdout bytes state).finalState := by
  apply reservationMetadataFrame_same_rows <;> first | rfl | exact Nat.le_refl _

theorem reservationMetadataFrame_replace (state : ConstructionState) (index : DestinationId)
    (before after : PendingDestination) (present : state.destinations[index]? = some before)
    (progress : after.progress = before.progress) :
    ReservationMetadataFrame state { state with destinations := state.destinations.set! index after } := by
  refine ⟨by simp, Nat.le_refl _, rfl, rfl, ?_⟩
  constructor
  intro queried initial final initialPresent finalPresent stable
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at finalPresent
  by_cases same : index = queried
  · subst queried
    have inside := (Array.getElem?_eq_some_iff.mp present).choose
    simp only [inside, ↓reduceIte, Option.some.injEq] at finalPresent
    have initialEq : initial = before := Option.some.inj (initialPresent.symm.trans present)
    subst initial
    subst final
    refine ⟨by simpa only [progress] using stable, ?_⟩
    intro count selected exiting
    exact ⟨count, selected, progress.symm.trans exiting, rfl⟩
  · have unchanged : initial = final := Option.some.inj (initialPresent.symm.trans
      (by simpa only [same, ↓reduceIte] using finalPresent))
    subst final
    exact ⟨stable, fun count selected exiting => ⟨count, selected, exiting, rfl⟩⟩

theorem reservationMetadataFrame_replace_events (state : ConstructionState) (index : DestinationId)
    (before after : PendingDestination) (storage : Array ReceivingStorage) (events : List ConstructionEvent)
    (present : state.destinations[index]? = some before)
    (size : state.storage.size ≤ storage.size)
    (other : ∀ queried, queried ≠ index → destinationObservations queried events = [])
    (transition : ReservationStableProgress before.progress →
      ReservationStableProgress after.progress ∧
        (∀ count selected, after.progress = .exiting count selected →
          ∃ oldCount oldSelected, before.progress = .exiting oldCount oldSelected ∧
            runDestinationTrace index .unseen (state.events ++ events) =
              runDestinationTrace index .unseen state.events)) :
    ReservationMetadataFrame state { state with
      storage := storage
      destinations := state.destinations.set! index after
      events := state.events ++ events } := by
  refine ⟨by simp, size, rfl, rfl, ?_⟩
  constructor
  intro queried initial final initialPresent finalPresent stable
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at finalPresent
  by_cases same : index = queried
  · subst queried
    have inside := (Array.getElem?_eq_some_iff.mp present).choose
    simp only [inside, ↓reduceIte, Option.some.injEq] at finalPresent
    have initialEq : initial = before := Option.some.inj (initialPresent.symm.trans present)
    subst initial
    subst final
    exact transition stable
  · have unchanged : initial = final := Option.some.inj (initialPresent.symm.trans
      (by simpa only [same, ↓reduceIte] using finalPresent))
    subst final
    refine ⟨stable, fun count selected exiting => ⟨count, selected, exiting, ?_⟩⟩
    rw [runDestinationTrace_append]
    simp only [runDestinationTrace, other queried (Ne.symm same), runDestinationObservations]
    cases runDestinationObservations .unseen (destinationObservations queried state.events) <;> rfl

theorem reservationMetadataFrame_emit_mutable (state : ConstructionState) (index : DestinationId)
    (destination : PendingDestination) (events : List ConstructionEvent)
    (present : state.destinations[index]? = some destination)
    (mutable : ¬ ReservationStableProgress destination.progress)
    (other : ∀ queried, queried ≠ index → destinationObservations queried events = []) :
    ReservationMetadataFrame state { state with events := state.events ++ events } := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl, ?_⟩
  constructor
  intro queried initial final initialPresent finalPresent stable
  have sameRow : initial = final := Option.some.inj (initialPresent.symm.trans finalPresent)
  subst final
  by_cases same : queried = index
  · subst queried
    have initialEq : initial = destination := Option.some.inj (initialPresent.symm.trans present)
    subst initial
    exact False.elim (mutable stable)
  · refine ⟨stable, fun count selected exiting => ⟨count, selected, exiting, ?_⟩⟩
    rw [runDestinationTrace_append]
    simp only [runDestinationTrace, other queried same, runDestinationObservations]
    cases runDestinationObservations .unseen (destinationObservations queried state.events) <;> rfl

theorem reservationMetadataFrame_push (state : ConstructionState) (destination : PendingDestination)
    (storage : Array ReceivingStorage) (events : List ConstructionEvent)
    (size : state.storage.size ≤ storage.size)
    (other : ∀ queried, queried < state.destinations.size → destinationObservations queried events = []) :
    ReservationMetadataFrame state { state with
      storage := storage
      destinations := state.destinations.push destination
      events := state.events ++ events } := by
  refine ⟨by simp, size, rfl, rfl, ?_⟩
  constructor
  intro queried initial final initialPresent finalPresent stable
  have inside := (Array.getElem?_eq_some_iff.mp initialPresent).choose
  have different : queried ≠ state.destinations.size := Nat.ne_of_lt inside
  simp only [Array.getElem?_push, different, ↓reduceIte] at finalPresent
  have unchanged : initial = final := Option.some.inj (initialPresent.symm.trans finalPresent)
  subst final
  refine ⟨stable, fun count selected exiting => ⟨count, selected, exiting, ?_⟩⟩
  rw [runDestinationTrace_append]
  simp only [runDestinationTrace, other queried inside, runDestinationObservations]
  cases runDestinationObservations .unseen (destinationObservations queried state.events) <;> rfl

theorem reservationMetadataFrame_successors (state : ConstructionState)
    (successors : List (DestinationId × DestinationId)) :
    ReservationMetadataFrame state { state with destinationSuccessors := successors } :=
  reservationMetadataFrame_same_rows state _ rfl rfl rfl rfl (Nat.le_refl _)

theorem reservationMetadataFrame_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : ∀ state, ReservationMetadataFrame state (action state).finalState)
    (remaining : ∀ value state, ReservationMetadataFrame state (next value state).finalState)
    (state : ConstructionState) : ReservationMetadataFrame state ((action >>= next) state).finalState := by
  have before := first state
  cases evaluated : action state with
  | fault reason final => simpa only [evaluated, bind, ConstructionResult.finalState] using before
  | ok value middle =>
      simp only [evaluated, ConstructionResult.finalState] at before
      simpa only [evaluated, bind] using before.trans (remaining value middle)

theorem reservedSnapshotPhase_frame (before after : ConstructionState) (snapshot : PendingDestination)
    (allocated : snapshot.capability.id < before.destinations.size)
    (frame : ReservationRowsFrame before after) (valid : ReservedSnapshotPhase before snapshot) :
    ReservedSnapshotPhase after snapshot := by
  intro final finalPresent
  obtain ⟨initial, initialPresent⟩ : ∃ initial,
      before.destinations[snapshot.capability.id]? = some initial := by
    exact ⟨before.destinations[snapshot.capability.id], Array.getElem?_eq_getElem allocated⟩
  have previous := valid initial initialPresent
  have stable : ReservationStableProgress initial.progress := by
    cases progress : initial.progress <;> simp_all [ReservationStableProgress]
  obtain ⟨stableAfter, exitingBefore⟩ := frame.preserves snapshot.capability.id initial final
    initialPresent finalPresent stable
  cases progress : final.progress <;> simp_all only [ReservationStableProgress]
  case exiting count selected =>
    obtain ⟨oldCount, oldSelected, oldProgress, trace⟩ := exitingBefore count selected rfl
    simp only [oldProgress] at previous
    intro phase accepted
    exact previous phase (trace ▸ accepted)

theorem destinationReservationStateValid_frame (before after : ConstructionState)
    (frame : ReservationMetadataFrame before after) (valid : DestinationReservationStateValid before) :
    DestinationReservationStateValid after := by
  constructor
  · intro token owner incoming selected snapshot present
    rw [frame.tickets] at present
    obtain ⟨bounds, selectedBound, earlier, phase⟩ := valid.active token owner incoming selected snapshot present
    refine ⟨bounds.mono frame.destinations frame.storage,
      Nat.lt_of_lt_of_le selectedBound frame.destinations, earlier, ?_⟩
    intro replaced
    obtain ⟨progress, phase⟩ := phase replaced
    exact ⟨progress, reservedSnapshotPhase_frame before after snapshot bounds.allocated frame.rows phase⟩
  · intro first second owner incoming selected snapshot otherOwner otherIncoming otherSelected otherSnapshot
      firstPresent secondPresent different selectedDifferent otherDifferent
    rw [frame.tickets] at firstPresent secondPresent
    exact valid.distinct first second owner incoming selected snapshot otherOwner otherIncoming otherSelected otherSnapshot
      firstPresent secondPresent different selectedDifferent otherDifferent
  · intro entry member
    rw [frame.resumptions] at member
    exact (valid.resumptions entry member).mono frame.destinations frame.storage

end Goose.Proofs.ConstructionExecutionProtocol
