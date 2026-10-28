import Goose.Proofs.ConstructionExitValidatedNonempty
import Goose.Proofs.ConstructionExitByteSetup
import Goose.Proofs.ConstructionExitReservationWritable

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem reserve_open_zero_direct (state : ConstructionState) (incoming : Nat) (row : PendingDestination)
    (present : state.destinations[incoming]? = some row) (opened : row.progress = .open 0)
    (current : destinationCurrent state incoming = .ok incoming) :
    reserveExitDestination incoming .newValue state =
      .ok (state.exitReservations.size, incoming) { state with exitReservations := state.exitReservations.push (.active .fresh incoming incoming row) } := by
  have renewal : renewReceivingDestination incoming state = .ok incoming state := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  have frontier : exitFrontierAction (state.destinations.size + 1) incoming state = .ok incoming state :=
    exitFrontier_open state.destinations.size incoming 0 state row present opened
  rw [reserveExitDestination_equation]
  simp only [show (ExitSource.newValue == ExitSource.namedResult) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, renewal, bind, ConstructionM.get, frontier,
    reserveLookupStep, lookupDestination_result, present, opened, Bool.true_or, pure, ConstructionM.set]

theorem direct_byte_exit_setup (source target : RuntimeActivation) (bytes : List UInt8)
    (origin : OriginId) (state : ExecutionState) (incoming : Nat) (row : PendingDestination)
    (channels : target.channels = [.construct incoming])
    (present : state.construction.destinations[incoming]? = some row) (opened : row.progress = .open 0)
    (current : destinationCurrent state.construction incoming = .ok incoming) :
    let token := state.construction.exitReservations.size
    let prepared := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.push (.active .fresh incoming incoming row) } }
    exitChannels source target [.bytes (.varr (.int .u8)) bytes origin] origin state = .ok [.construct incoming] prepared ∧
    exitChannelReservationTokens state.construction.exitReservations.size prepared = [token] ∧
    prepared.construction.exitReservations[token]? = some (.active .fresh incoming incoming row) := by
  have reservation := reserve_open_zero_direct state.construction incoming row present opened current
  dsimp only
  constructor
  · simp only [exitChannels, channels, List.length_cons, List.length_nil, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.mapM_cons,
      List.mapM_nil, exitSource, receivingDestination, liftConstruction, current, bind, pure, reservation]
  · constructor
    · simp [exitChannelReservationTokens]
    · simp

theorem direct_packed_byte_first_write (state : ConstructionState) (incoming : Nat)
    (row : PendingDestination) (storage : ReceivingStorage) (byte : UInt8)
    (present : state.destinations[incoming]? = some row)
    (stored : state.storage[row.storage]? = some storage)
    (opened : row.progress = .open 0) (current : destinationCurrent state incoming = .ok incoming)
    (receiver : row.use = .receiver) (packed : row.layout = .packed) (adaptation : row.adaptation = none) :
    ∃ reserved written,
      reserveExitDestination incoming .newValue state = .ok (state.exitReservations.size, incoming) reserved ∧
      writeElement incoming ⟨#[byte]⟩ reserved = .ok () written := by
  let reserved := { state with exitReservations := state.exitReservations.push (.active .fresh incoming incoming row) }
  have reservation := reserve_open_zero_direct state incoming row present opened current
  have found : reserved.destinations[incoming]? = some row := present
  have backing : reserved.storage[row.storage]? = some storage := stored
  have writable := receiver_destination_writable reserved incoming row found receiver
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have storageInside := (Array.getElem?_eq_some_iff.mp backing).1
  have write : ∃ after, writeElement incoming ⟨#[byte]⟩ reserved = .ok () after := by
    simp only [writeElement, writableDestination_result, found, writable, bind, opened, lookupStorage_result, backing]
    cases backingKind : row.backing <;>
      simp only [writingAvailable_result, backingKind, packed, adaptation, Option.map_none, Option.getD_none,
        receiver, show 0 + 1 < 2 ^ 32 by decide, decide_true, Bool.true_and, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, pure, bind, replaceStorage_result, storageInside,
        replaceDestination_result, inside, emit_result]
    all_goals exact ⟨_, rfl⟩
  obtain ⟨written, write⟩ := write
  exact ⟨reserved, written, reservation, write⟩

def recursiveDirectFirstByteObservation : Bool :=
  let state := Goose.Proofs.Exit.stepState (runModule 28 ⟨.release, Goose.Proofs.ExitExecutionChecks.recursiveDestinations⟩ .initial)
  match reserveExitDestination 1 .newValue state.construction with
  | .ok (0, 1) reserved =>
    match writeElement 1 ⟨#[66]⟩ reserved with
    | .ok () _ => true
    | _ => false
  | _ => false

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem recursive_direct_first_byte : recursiveDirectFirstByteObservation = true := by
  cbv

#print axioms recursive_direct_first_byte
#print axioms direct_packed_byte_first_write
#print axioms reserve_open_zero_direct
#print axioms direct_byte_exit_setup

end Goose.Proofs.ConstructionAcceptedExecution
