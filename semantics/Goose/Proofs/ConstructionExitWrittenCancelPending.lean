import Goose.Proofs.ConstructionExitWrittenCancelRegions
import Goose.Proofs.ConstructionExitFreshCancelPending

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ExitExecution

theorem allocated_byte_write_cancel_pending (config : EvalConfig) (initialized : Nat) (owner : ActId)
    (origin : OriginId) (knownCount : Option Nat) (byte : UInt8)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout owner (.varr (.int .u8)) .value origin none knownCount before = .ok id allocated) :
    ∃ reserved written final,
      reserveExitDestination id .newValue allocated.construction = .ok (allocated.construction.exitReservations.size, id) reserved ∧
      writeElement id ⟨#[byte]⟩ reserved = .ok () written ∧
      (do cancelExitReservation allocated.construction.exitReservations.size []
          releaseExitReservation allocated.construction.exitReservations.size) written = .ok () final ∧
      ∀ frame ∈ pending, CarriersLandingReady { allocated with construction := final } frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout { allocated with construction := final } carrier := by
  obtain ⟨reserved, written, final, reserve, write, cancel, rooted, rows, storage⟩ :=
    allocated_byte_write_cancel_frame config initialized owner origin knownCount byte before allocated id ambient types live regions pending world created
  obtain ⟨⟨backing⟩, _⟩ := newDestination_open_ready config initialized owner (.varr (.int .u8)) .value origin knownCount
    before allocated ambient types live regions pending id (.int .u8) world rfl created
  obtain ⟨row, found, packed, _, _, receiver, adaptation⟩ :=
    newDestination_byteOwner_packed_value_with_adaptation config.layout owner origin knownCount before allocated id created
  have same : row = backing.destination := Option.some.inj (found.symm.trans backing.present)
  subst row
  have current := newDestination_current_self config initialized owner (.varr (.int .u8)) .value origin knownCount before allocated id
    ambient types live regions pending world created
  let expected := { allocated.construction with
    exitReservations := allocated.construction.exitReservations.push (.active .fresh id id backing.destination) }
  have actualReserve := reserve_open_zero_direct allocated.construction id backing.destination backing.present backing.opened current
  have equal : reserved = expected := (ConstructionResult.ok.inj (reserve.symm.trans actualReserve)).2
  subst reserved
  have reservedCurrent : destinationCurrent expected id = .ok id :=
    (destinationCurrent_congr_tables allocated.construction expected rfl rfl id).trans current
  have allocatedWorld := newDestination_acceptedWorld config owner (.varr (.int .u8)) .value origin knownCount initialized before allocated id
    ambient types live regions pending world created
  have lifecycle := reserveExitDestination_reservation_lifecycle id .newValue allocated.construction allocatedWorld.ownership.source.structural.1.1
  rw [actualReserve] at lifecycle
  simp only [ConstructionResult.finalState] at lifecycle
  have ticket : expected.exitReservations[allocated.construction.exitReservations.size]? = some (.active .fresh id id backing.destination) := by
    simp [expected]
  obtain ⟨otherWritten, nextStorage, otherWrite, nextPresent, nextStored, nextCurrent⟩ :=
    packed_receiver_write_step expected id 0 backing.destination backing.storage byte backing.present backing.bytes backing.opened
      packed adaptation receiver reservedCurrent (by decide)
  have sameWritten : otherWritten = written := (ConstructionResult.ok.inj (otherWrite.symm.trans write)).2
  subst otherWritten
  let nextRow := { backing.destination with progress := DestinationProgress.open (0 + 1), writeEnd := backing.destination.writeEnd + 1 }
  have metadata := writeElement_reservation_frame id ⟨#[byte]⟩ expected lifecycle.1
  rw [write] at metadata
  simp only [ConstructionResult.finalState] at metadata
  have destLife := writeElement_destination_lifecycle_invariant id ⟨#[byte]⟩ expected lifecycle.1
  rw [write] at destLife
  simp only [ConstructionResult.finalState] at destLife
  have writtenLife : ReservationLifecycleInvariant written := ⟨destLife, destinationReservationStateValid_frame expected written metadata lifecycle.2⟩
  have writtenTicket : written.exitReservations[allocated.construction.exitReservations.size]? =
      some (.active .fresh id id backing.destination) := by rw [metadata.tickets]; exact ticket
  have indexing := writeElement_preserves_indexing id ⟨#[byte]⟩ expected
  rw [write] at indexing
  simp only [ConstructionResult.finalState] at indexing
  have newest := (newDestination_newest_receiver config.layout owner (.varr (.int .u8)) .value origin knownCount before allocated id created).1
  have writtenNewest : written.destinations.size = id + 1 := indexing.1.trans newest
  have nextFound : written.destinations[id]? = some nextRow := nextPresent
  have nextStore : written.storage[nextRow.storage]? = some nextStorage := nextStored
  have leaf := newest_active_destination_is_leaf written id nextRow nextFound (by simp [activeRow, nextRow])
    writtenNewest writtenLife.1.2.1 writtenLife.1.2.2.2
  have writable := receiver_destination_writable written id nextRow nextFound receiver
  have direct : id = backing.destination.capability.id := (lifecycle.1.2.1 id backing.destination backing.present).symm
  let cleaned := abandonRowState written id nextRow nextStorage
  let cancelled := { cleaned with
    destinationResumptions := (id, backing.destination) :: cleaned.destinationResumptions
    exitReservations := cleaned.exitReservations.set! allocated.construction.exitReservations.size .restored }
  let exactFinal := { cancelled with exitReservations := cancelled.exitReservations.set! allocated.construction.exitReservations.size .released }
  have exactCancel : (do
      cancelExitReservation allocated.construction.exitReservations.size []
      releaseExitReservation allocated.construction.exitReservations.size) written = .ok () exactFinal :=
    cancelled_leaf_exact written allocated.construction.exitReservations.size id id id 1 backing.destination nextRow nextStorage
      writtenTicket nextCurrent nextFound (writtenLife.1.2.1 id nextRow nextFound) (Or.inl rfl) writable nextStore leaf direct
  have sameFinal : final = exactFinal := (ConstructionResult.ok.inj (cancel.symm.trans exactCancel)).2
  subst final
  obtain ⟨allocation⟩ := newDestination_fresh_frame config.layout owner (.varr (.int .u8)) .value origin knownCount before allocated id
    world.ownership.source.structural.1.1.1 created
  have fresh := newDestination_fresh_id config.layout owner (.varr (.int .u8)) .value origin knownCount before allocated id created
  have allocationRow : allocation.row = backing.destination := by
    have prior : allocated.construction.destinations[id]? = some allocation.row := by rw [allocation.destinations, fresh]; exact Array.getElem?_push_size
    exact Option.some.inj (prior.symm.trans backing.present)
  let beforeReleased := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push .released } }
  have fullFrame : FreshDestinationFrame beforeReleased { allocated with construction := exactFinal } := by
    refine ⟨?_, { nextRow with progress := .abandoned }, ?_, ?_, ?_, ?_, ?_⟩
    · change { allocated with construction := exactFinal } = { beforeReleased with construction := exactFinal }
      rw [allocation.outer]
    · change exactFinal.destinations = before.construction.destinations.push { nextRow with progress := .abandoned }
      have transition := writeElement_transition id ⟨#[byte]⟩ expected
      rw [write] at transition
      cases transition with
      | written actual oldStorage count actualFound actualStored actualOpened =>
        have sameRow : actual = backing.destination := Option.some.inj (actualFound.symm.trans backing.present)
        subst actual
        have sameCount : count = 0 := DestinationProgress.open.inj (actualOpened.symm.trans backing.opened)
        subst count
        simp only [exactFinal, cancelled, cleaned, abandonRowState, nextRow, ByteArray.size]
        simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds, expected]
        rw [allocation.destinations, allocationRow]
        simp [fresh, Array.setIfInBounds, Array.set_push]
    · exact receiver
    · exact indexing.2.trans allocation.successors
    · change exactFinal.exitReservations = before.construction.exitReservations.push .released
      simp [exactFinal, cancelled, cleaned, abandonRowState, metadata.tickets, expected, allocation.tickets,
        Array.set!_eq_setIfInBounds, Array.setIfInBounds, Array.set_push]
    · intro index prior present
      exact storage index prior present
  refine ⟨expected, written, exactFinal, actualReserve, write, cancel, ?_⟩
  intro frame member
  have ready := appended_ticket_pending_carrier_ready config initialized before ambient types live regions pending .released world frame member
  have backing := appended_ticket_pending_carrier_backing config initialized before ambient types live regions pending .released world frame member
  exact ⟨fullFrame.carriers_ready frame.channels frame.carriers ready,
    fun carrier carried => fullFrame.carrier_backing config.layout carrier (backing carrier carried)⟩

#print axioms allocated_byte_write_cancel_pending

end Goose.Proofs.ConstructionAcceptedExecution
