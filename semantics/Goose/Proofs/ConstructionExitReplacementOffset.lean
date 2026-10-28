import Goose.Proofs.ConstructionExitReplacementOpen
import Goose.Proofs.ConstructionExecutionProtocolReservationCombinators
import Goose.Proofs.ConstructionExitByteFinishParent
import Goose.Proofs.ConstructionAcceptedOpenDestination
import Goose.Proofs.ExitExecutionStoragePrefixReads

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecution
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership

theorem open_replacement_start (before after : ConstructionState) (incoming selected count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some row) (opened : row.progress = .open count)
    (stored : before.storage[row.storage]? = some storage)
    (executed : openExitReplacement incoming before = .ok selected after) :
    ∃ replacement, after.destinations[selected]? = some replacement ∧
      replacement.capability.start = storage.bytes.size := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [openExitReplacement, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite before incoming with
  | false => simp [allowed] at executed
  | true =>
    simp only [allowed, opened, pure, bind, lookupStorage_result, stored, ConstructionM.get,
      ConstructionM.set, replaceDestination_result, replaceStorage_result, emit_result,
      Array.size_push, Nat.lt_succ_of_lt inside, storageInside, Array.size_setIfInBounds, ↓reduceIte] at executed
    split at executed <;>
      simp only [Nat.lt_succ_of_lt inside, storageInside, ↓reduceIte, bind, pure] at executed <;>
      cases executed <;>
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne,
        Nat.ne_of_lt inside, Array.getElem?_push]

theorem reserve_open_replacement_start (before after : ConstructionState) (incoming selected token count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some row) (opened : row.progress = .open (count + 1))
    (stored : before.storage[row.storage]? = some storage)
    (current : destinationCurrent before incoming = .ok incoming)
    (reserved : reserveExitDestination incoming .newValue before = .ok (token, selected) after) :
    ∃ replacement, after.destinations[selected]? = some replacement ∧ replacement.capability.start = storage.bytes.size := by
  have renewal : renewReceivingDestination incoming before = .ok incoming before := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  have frontier : exitFrontierAction (before.destinations.size + 1) incoming before = .ok incoming before :=
    exitFrontier_open before.destinations.size incoming (count + 1) before row present opened
  rw [reserveExitDestination_equation] at reserved
  simp only [show (ExitSource.newValue == ExitSource.namedResult) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, renewal, bind, ConstructionM.get, frontier,
    reserveLookupStep, lookupDestination_result, present, opened, Bool.false_or] at reserved
  cases replacement : openExitReplacement incoming before with
  | fault reason state => simp only [replacement] at reserved; cases reserved
  | ok picked state =>
    simp only [replacement, ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.ok.injEq] at reserved
    obtain ⟨samePair, rfl⟩ := reserved
    cases samePair
    exact open_replacement_start before state incoming selected (count + 1) row storage present opened stored replacement

theorem reserved_byte_start_order (layout : LayoutEnv)
    (reservationBefore reserved : ConstructionState) (incoming selected token count : Nat)
    (receiverState : ExecutionState) (receiverConstruction : receiverState.construction = reservationBefore)
    (receiver : OpenDestinationBacking layout receiverState incoming (.varr (.int .u8)) (count + 1))
    (receiverCurrent : destinationCurrent reservationBefore incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue reservationBefore = .ok (token, selected) reserved) :
    ∃ replacement, reserved.destinations[selected]? = some replacement ∧
      receiver.destination.capability.start ≤ replacement.capability.start := by
  have receiverPresent : reservationBefore.destinations[incoming]? = some receiver.destination := by
    simpa only [receiverConstruction] using receiver.present
  have receiverStored : reservationBefore.storage[receiver.destination.storage]? = some receiver.storage := by
    simpa only [receiverConstruction] using receiver.bytes
  obtain ⟨replacement, replacementPresent, replacementStart⟩ := reserve_open_replacement_start
    reservationBefore reserved incoming selected token count receiver.destination receiver.storage receiverPresent
    receiver.opened receiverStored receiverCurrent reservation
  have start := elementsEnd_monotone receiver.fuel layout receiver.element (count + 1) receiver.storage.bytes
    (destinationPayloadStart receiver.destination) receiver.destination.writeEnd receiver.scan
  have initialBound : receiver.destination.capability.start ≤ receiver.storage.bytes.size := by
    unfold destinationPayloadStart at start
    have upper := receiver.bounded
    omega
  exact ⟨replacement, replacementPresent, by simpa only [replacementStart] using initialBound⟩

#print axioms reserved_byte_start_order

#print axioms reserve_open_replacement_start
#print axioms open_replacement_start

end Goose.Proofs.ConstructionAcceptedExecution
