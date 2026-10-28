import Goose.Proofs.ConstructionExitProducedFrame

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ExitExecutionChecks

def recursiveByteExit : ExecutionStep Flow :=
  let state := Goose.Proofs.Exit.stepState (runModule 28 ⟨.release, recursiveDestinations⟩ .initial)
  match state.activations.head? with
  | some source => execStmt 100 ⟨.release, recursiveDestinations⟩ source
      (.returnFrom 0 [.bytes array [66] 0] 0) state
  | none => .stop (.fault .unbound) state

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem recursive_byte_exit_observation :
    exitObservation recursiveByteExit = some (⟨2, .nonlocal 0⟩, [.completed 1]) := by
  cbv

def recursiveByteReceiverObservation : Option (List Channel × Option DestinationProgress) :=
  let state := Goose.Proofs.Exit.stepState (runModule 28 ⟨.release, recursiveDestinations⟩ .initial)
  match targetActivation ⟨.release, recursiveDestinations⟩ 0 state with
  | .ok target _ => some (target.channels, state.construction.destinations[1]?.map (·.progress))
  | _ => none

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem recursive_byte_receiver_open :
    recursiveByteReceiverObservation = some ([.construct 1], some (.open 0)) := by
  cbv

def recursiveByteReservationObservation : Option (Nat × Nat) :=
  let state := Goose.Proofs.Exit.stepState (runModule 28 ⟨.release, recursiveDestinations⟩ .initial)
  match reserveExitDestination 1 .newValue state.construction with
  | .ok pair _ => some pair
  | _ => none

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem recursive_byte_direct_reservation : recursiveByteReservationObservation = some (0, 1) := by
  cbv

theorem validated_recursive_direct_return :
    validate recursiveDestinations = .ok () ∧
    timeoutActivations (runModule 28 ⟨.release, recursiveDestinations⟩ .initial) = some ([3, 2, 1, 0], 4) ∧
    recursiveByteReceiverObservation = some ([.construct 1], some (.open 0)) ∧
    recursiveByteReservationObservation = some (0, 1) ∧
    exitObservation recursiveByteExit = some (⟨2, .nonlocal 0⟩, [.completed 1]) ∧
    returnedObservation (eval 200 .release recursiveDestinations) =
      some ([66, 10, 65, 10], [.begin 0, .begin 1, .write 1 0, .publish 1, .write 0 0, .publish 0]) := by
  exact ⟨validated_nonempty_nested_return_witness.1, recursive_live_activations, recursive_byte_receiver_open,
    recursive_byte_direct_reservation, recursive_byte_exit_observation, recursiveDestinations_execution⟩

#print axioms recursive_byte_exit_observation
#print axioms recursive_byte_receiver_open
#print axioms recursive_byte_direct_reservation
#print axioms validated_recursive_direct_return

end Goose.Proofs.ConstructionAcceptedExecution
