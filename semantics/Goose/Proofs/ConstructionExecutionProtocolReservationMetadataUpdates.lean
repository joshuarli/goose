import Goose.Proofs.ConstructionExecutionProtocolReservationLeaves
import Goose.Proofs.ConstructionExecutionProtocolDestination

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem reservationMetadataFrame_storage (state : ConstructionState)
    (storage : Array ReceivingStorage) (size : state.storage.size ≤ storage.size) :
    ReservationMetadataFrame state { state with storage := storage } :=
  reservationMetadataFrame_same_rows state _ rfl rfl rfl rfl size

theorem reservationMetadataFrame_replace_mutable (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (storage : Array ReceivingStorage) (events : List ConstructionEvent)
    (present : state.destinations[id]? = some before)
    (size : state.storage.size ≤ storage.size)
    (mutable : ¬ ReservationStableProgress before.progress)
    (other : ∀ queried, queried ≠ id → destinationObservations queried events = []) :
    ReservationMetadataFrame state { state with
      storage := storage
      destinations := state.destinations.set! id after, events := state.events ++ events } := by
  apply reservationMetadataFrame_replace_events state id before after storage events present size other
  intro stable
  exact False.elim (mutable stable)

theorem reservationMetadataFrame_replace_terminal (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (storage : Array ReceivingStorage) (events : List ConstructionEvent)
    (present : state.destinations[id]? = some before)
    (size : state.storage.size ≤ storage.size)
    (terminal : ReservationStableProgress after.progress)
    (notExiting : ∀ count selected, after.progress ≠ .exiting count selected)
    (other : ∀ queried, queried ≠ id → destinationObservations queried events = []) :
    ReservationMetadataFrame state { state with
      storage := storage
      destinations := state.destinations.set! id after, events := state.events ++ events } := by
  apply reservationMetadataFrame_replace_events state id before after storage events present size other
  intro _
  exact ⟨terminal, fun count selected progress => False.elim (notExiting count selected progress)⟩

theorem reservationMetadataFrame_two_mutable (state : ConstructionState) (first second : DestinationId)
    (beforeFirst beforeSecond : PendingDestination) (firstEvents secondEvents : List ConstructionEvent)
    (afterFirst afterSecond : PendingDestination) (storage : Array ReceivingStorage)
    (size : state.storage.size ≤ storage.size)
    (firstPresent : state.destinations[first]? = some beforeFirst)
    (secondPresent : state.destinations[second]? = some beforeSecond)
    (different : first ≠ second)
    (firstMutable : ¬ ReservationStableProgress beforeFirst.progress)
    (secondMutable : ¬ ReservationStableProgress beforeSecond.progress)
    (firstOther : ∀ queried, queried ≠ first → destinationObservations queried firstEvents = [])
    (secondOther : ∀ queried, queried ≠ second → destinationObservations queried secondEvents = []) :
    ReservationMetadataFrame state { state with
      storage := storage
      destinations := (state.destinations.set! first afterFirst).set! second afterSecond
      events := (state.events ++ firstEvents) ++ secondEvents } := by
  let stored : ConstructionState := { state with storage := storage }
  let changed : ConstructionState := { stored with
    destinations := stored.destinations.set! first afterFirst
    events := stored.events ++ firstEvents }
  have firstFrame : ReservationMetadataFrame stored changed :=
    reservationMetadataFrame_replace_mutable stored first beforeFirst afterFirst storage firstEvents
      firstPresent (Nat.le_refl _) firstMutable firstOther
  have secondPresent' : changed.destinations[second]? = some beforeSecond := by
    simpa only [changed, stored, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne different] using secondPresent
  have secondFrame := reservationMetadataFrame_replace_mutable changed second beforeSecond afterSecond
    storage secondEvents secondPresent' (Nat.le_refl _) secondMutable secondOther
  exact (reservationMetadataFrame_storage state storage size).trans (firstFrame.trans secondFrame)

#print axioms reservationMetadataFrame_storage
#print axioms reservationMetadataFrame_replace_mutable
#print axioms reservationMetadataFrame_replace_terminal

end Goose.Proofs.ConstructionExecutionProtocol
