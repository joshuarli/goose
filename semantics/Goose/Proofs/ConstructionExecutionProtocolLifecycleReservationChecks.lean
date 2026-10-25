import Goose.Proofs.ConstructionExecutionProtocolReservations
import Goose.Proofs.ConstructionExecutionProtocolReservationKernel

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol.LifecycleReservationCounterexample

open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

private def capability (id : Nat) : Goose.Core.Destination Goose.Construct.Ty :=
  { id := id
    receiver := ⟨.global 0, []⟩
    layout := .unit
    logicalType := .unit
    request := .value
    start := 0
    owner := 0 }

private def currentParent : PendingDestination :=
  ⟨capability 0, .direct 0, .packed, .receiver, .exiting 0 1, 0, 0, none, none⟩

private def selectedReplacement : PendingDestination :=
  ⟨capability 1, .direct 0, .packed, .replacement 0, .abandoned, 0, 0, none, none⟩

private def invalidSnapshot : PendingDestination :=
  ⟨capability 0, .direct 9, .packed, .receiver, .built 0, 0, 0, none, none⟩

private def currentState : ConstructionState :=
  { ConstructionState.initial with
    storage := #[⟨ByteArray.empty, 0⟩]
    destinations := #[currentParent, selectedReplacement]
    events := [.begin 0, .begin 1, .abandon 1]
    exitReservations := #[.active .fresh 0 1 invalidSnapshot] }

private theorem current_lifecycle : DestinationLifecycleInvariant currentState := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro id
    cases id with
    | zero =>
      simp [currentState, currentParent, selectedReplacement, invalidSnapshot, capability,
        destinationObservations, observeDestination, runDestinationTrace,
        runDestinationObservations, destinationTraceStep, DestinationTracePhase.matchesDestination,
        DestinationTracePhase.matchesProgress]
    | succ id =>
      cases id with
      | zero =>
        simp [currentState, currentParent, selectedReplacement, invalidSnapshot, capability,
          destinationObservations, observeDestination, runDestinationTrace,
          runDestinationObservations, destinationTraceStep, DestinationTracePhase.matchesDestination,
          DestinationTracePhase.matchesProgress]
      | succ id =>
        simp [currentState, currentParent, selectedReplacement, invalidSnapshot, capability,
          destinationObservations, observeDestination, runDestinationTrace,
          runDestinationObservations]
  · intro id destination present
    cases id with
    | zero =>
      simp [currentState] at present
      cases present
      simp [currentParent, capability]
    | succ id => cases id with
      | zero =>
        simp [currentState] at present
        cases present
        simp [selectedReplacement, capability]
      | succ id => simp [currentState, currentParent, selectedReplacement, invalidSnapshot, capability] at present
  · intro id destination present
    cases id with
    | zero =>
      simp [currentState] at present
      cases present
      simp [currentParent, capability, PendingDestination.storage,
        DestinationBacking.writeStorage, DestinationBacking.receiverStorage, currentState]
    | succ id => cases id with
      | zero =>
        simp [currentState] at present
        cases present
        simp [currentParent, selectedReplacement, capability, PendingDestination.storage,
          DestinationBacking.writeStorage, DestinationBacking.receiverStorage, currentState]
      | succ id => simp [currentState, currentParent, selectedReplacement, invalidSnapshot, capability] at present
  · intro id destination present
    cases id with
    | zero =>
      simp [currentState] at present
      cases present
      simp [currentParent, capability]
    | succ id => cases id with
      | zero =>
        simp [currentState] at present
        cases present
        simp [selectedReplacement, capability]
      | succ id => simp [currentState, currentParent, selectedReplacement, invalidSnapshot, capability] at present

private theorem cancel_restores_invalid_storage :
    ¬ DestinationLifecycleInvariant (cancelExitReservation 0 [] currentState).finalState := by
  intro valid
  have present : (cancelExitReservation 0 [] currentState).finalState.destinations[0]? =
      some invalidSnapshot := by with_unfolding_all rfl
  have references := valid.2.2.1 0 invalidSnapshot present
  have storageSize : (cancelExitReservation 0 [] currentState).finalState.storage.size = 1 := by
    with_unfolding_all rfl
  simp [invalidSnapshot, PendingDestination.storage, DestinationBacking.writeStorage,
    DestinationBacking.receiverStorage, storageSize] at references

end Goose.Proofs.ConstructionExecutionProtocol.LifecycleReservationCounterexample

namespace Goose.Proofs.ConstructionExecutionProtocol

theorem destination_lifecycle_reservations_require_snapshot_bounds :
    ¬ ConstructionReservationPrimitives Goose.Construct.DestinationLifecycleInvariant := by
  intro primitives
  exact LifecycleReservationCounterexample.cancel_restores_invalid_storage
    (primitives.preserves _ (.cancelExitReservation 0 [])
      LifecycleReservationCounterexample.currentState
      LifecycleReservationCounterexample.current_lifecycle)

end Goose.Proofs.ConstructionExecutionProtocol
