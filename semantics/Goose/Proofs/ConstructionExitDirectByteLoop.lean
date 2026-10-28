import Goose.Proofs.ConstructionExitDirectByteSetup
import Goose.Proofs.ConstructionExitReservationWriteLoop

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ExitExecution

theorem packed_receiver_write_step (state : ConstructionState) (id count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage) (byte : UInt8)
    (present : state.destinations[id]? = some row) (stored : state.storage[row.storage]? = some storage)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (adaptation : row.adaptation = none) (use : row.use = .receiver)
    (current : destinationCurrent state id = .ok id) (fits : count + 1 < 2 ^ 32) :
    ∃ after nextStorage,
      writeElement id ⟨#[byte]⟩ state = .ok () after ∧
      after.destinations[id]? = some { row with progress := .open (count + 1), writeEnd := row.writeEnd + 1 } ∧
      after.storage[row.storage]? = some nextStorage ∧ destinationCurrent after id = .ok id := by
  have writable := receiver_destination_writable state id row present use
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  have existsWrite : ∃ after, writeElement id ⟨#[byte]⟩ state = .ok () after := by
    simp only [writeElement, writableDestination_result, present, writable, bind, opened, lookupStorage_result, stored]
    cases backing : row.backing <;>
      simp only [writingAvailable_result, backing, packed, adaptation, Option.map_none, Option.getD_none,
        use, fits, decide_true, Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        pure, bind, replaceStorage_result, storageInside, replaceDestination_result, inside, emit_result]
    all_goals exact ⟨_, rfl⟩
  obtain ⟨after, write⟩ := existsWrite
  have destination := writeElement_success_destination id ⟨#[byte]⟩ state after row count present opened write
  have indexing := writeElement_preserves_indexing id ⟨#[byte]⟩ state
  rw [write] at indexing
  simp only [ConstructionResult.finalState] at indexing
  have currentAfter : destinationCurrent after id = .ok id := by
    rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ state after indexing.1 indexing.2, indexing.1]
    simpa only [destinationCurrent_result] using current
  have transition := writeElement_transition id ⟨#[byte]⟩ state
  rw [write] at transition
  cases transition with
  | written actual oldStorage actualCount found storageFound phase =>
    have same := Option.some.inj (found.symm.trans present)
    subst actual
    have sameStorage := Option.some.inj (storageFound.symm.trans stored)
    subst oldStorage
    have sameCount := DestinationProgress.open.inj (phase.symm.trans opened)
    subst actualCount
    let nextStorage := { storage with bytes := storage.bytes.extract 0 row.writeEnd ++ (⟨#[byte]⟩ : ByteArray) ++ storage.bytes.extract (row.writeEnd + (⟨#[byte]⟩ : ByteArray).size) storage.bytes.size }
    refine ⟨_, nextStorage, write, ?_, ?_, currentAfter⟩
    · simpa [ByteArray.size] using destination.1
    · exact Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp stored).1

theorem packed_receiver_byte_loop (bytes : List UInt8) (origin : OriginId)
    (state : ExecutionState) (id count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (present : state.construction.destinations[id]? = some row) (stored : state.construction.storage[row.storage]? = some storage)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (adaptation : row.adaptation = none) (use : row.use = .receiver)
    (request : row.capability.request = .value)
    (current : destinationCurrent state.construction id = .ok id) (fits : count + bytes.length < 2 ^ 32) :
    ∃ after finalRow finalStorage,
      ((forIn bytes PUnit.unit fun byte _ => do
        receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
        pure (.yield PUnit.unit)) : EvalM PUnit) state = .ok PUnit.unit after ∧
      after.construction.destinations[id]? = some finalRow ∧
      after.construction.storage[finalRow.storage]? = some finalStorage ∧
      finalRow.progress = .open (count + bytes.length) ∧ finalRow.layout = .packed ∧
      finalRow.adaptation = none ∧ finalRow.use = .receiver ∧
      finalRow.capability.request = .value ∧ destinationCurrent after.construction id = .ok id := by
  induction bytes generalizing state row storage count with
  | nil =>
    exact ⟨state, row, storage, by simp [pure], present, stored, by simpa using opened,
      packed, adaptation, use, request, current⟩
  | cons byte rest ih =>
    have renewal : renewReceivingDestination id state.construction = .ok id state.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
        lookupDestination_result, present, opened]
    have stepFits : count + 1 < 2 ^ 32 := by simp only [List.length_cons] at fits; omega
    obtain ⟨written, nextStorage, write, nextPresent, nextStored, nextCurrent⟩ :=
      packed_receiver_write_step state.construction id count row storage byte
        present stored opened packed adaptation use current stepFits
    let nextRow := { row with progress := .open (count + 1), writeEnd := row.writeEnd + 1 }
    have tailFits : (count + 1) + rest.length < 2 ^ 32 := by simp only [List.length_cons] at fits; omega
    obtain ⟨after, finalRow, finalStorage, tail, finalFound, finalStored, finalPhase,
      finalPacked, finalAdaptation, finalUse, finalRequest, finalCurrent⟩ :=
      ih { state with construction := written } (count + 1) nextRow nextStorage nextPresent nextStored rfl
        packed adaptation use request nextCurrent tailFits
    refine ⟨after, finalRow, finalStorage, ?_, finalFound, finalStored, ?_,
      finalPacked, finalAdaptation, finalUse, finalRequest, finalCurrent⟩
    · simp only [List.forIn_cons, receivingAction, liftConstruction, renewal, bind, write, pure]
      exact tail
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPhase

theorem packed_receiver_byte_build (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (bytes : List UInt8) (origin : OriginId) (state : ExecutionState)
    (id count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (present : state.construction.destinations[id]? = some row) (stored : state.construction.storage[row.storage]? = some storage)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (adaptation : row.adaptation = none) (use : row.use = .receiver)
    (request : row.capability.request = .value)
    (current : destinationCurrent state.construction id = .ok id) (fits : count + bytes.length < 2 ^ 32) :
    ∃ after, buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) state = .ok () after := by
  have renewal : renewReceivingDestination id state.construction = .ok id state.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  obtain ⟨middle, finalRow, finalStorage, loop, finalFound, finalStored, finalOpened,
    finalPacked, finalAdaptation, finalUse, finalRequest, finalCurrent⟩ :=
    packed_receiver_byte_loop bytes origin state id count row storage present stored opened packed adaptation use request current fits
  have writable := receiver_destination_writable middle.construction id finalRow finalFound finalUse
  obtain ⟨finished, finish⟩ := packed_finish_success middle.construction id (count + bytes.length)
    finalRow finalStorage finalFound finalStored finalOpened finalPacked finalRequest writable
  have finalRenewal : renewReceivingDestination id middle.construction = .ok id middle.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, finalCurrent, pure,
      lookupDestination_result, finalFound, finalOpened]
  have body : (do
      for byte in bytes do receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      receivingAction origin id finishDestination) state = .ok () { middle with construction := finished } := by
    simp only [bind] at loop ⊢
    rw [loop]
    simp only [receivingAction, liftConstruction, finalRenewal, finish, bind, pure]
  refine ⟨{ middle with construction := finished }, ?_⟩
  simp only [buildExpr, liftConstruction, renewal, bind]
  change protectDestination origin id
    (do
      for byte in bytes do receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      receivingAction origin id finishDestination) state = _
  simp only [protectDestination, body]

theorem direct_reserved_byte_build (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (bytes : List UInt8) (origin : OriginId) (state : ExecutionState)
    (id : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (present : state.construction.destinations[id]? = some row)
    (stored : state.construction.storage[row.storage]? = some storage)
    (opened : row.progress = .open 0) (packed : row.layout = .packed)
    (adaptation : row.adaptation = none) (use : row.use = .receiver)
    (request : row.capability.request = .value)
    (current : destinationCurrent state.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    ∃ reserved after,
      reserveExitDestination id .newValue state.construction = .ok (state.construction.exitReservations.size, id) reserved ∧
      buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin)
        { state with construction := reserved } = .ok () after := by
  let reserved := { state.construction with exitReservations :=
    state.construction.exitReservations.push (.active .fresh id id row) }
  have reservation := reserve_open_zero_direct state.construction id row present opened current
  have reservedCurrent : destinationCurrent reserved id = .ok id := by
    rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ state.construction reserved rfl rfl]
    simpa only [destinationCurrent_result] using current
  obtain ⟨after, built⟩ := packed_receiver_byte_build fuel config environment bytes origin
    { state with construction := reserved } id 0 row storage present stored opened packed adaptation use request reservedCurrent (by simpa using fits)
  exact ⟨reserved, after, reservation, built⟩

#print axioms direct_reserved_byte_build
#print axioms packed_receiver_byte_loop
#print axioms packed_receiver_byte_build
#print axioms packed_receiver_write_step

end Goose.Proofs.ConstructionAcceptedExecution
