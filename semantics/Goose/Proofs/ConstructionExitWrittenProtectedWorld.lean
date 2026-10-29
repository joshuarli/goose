import Goose.Proofs.ConstructionExitProtectedCancel

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ExitExecution

private theorem protected_lift_sequence (origin : OriginId) (first : ConstructionM Unit) (second : ConstructionM Unit)
    (state : ExecutionState) :
    (do liftConstruction origin first; liftConstruction origin second) state =
      liftConstruction origin (do first; second) state := by
  simp only [bind, liftConstruction]
  cases result : first state.construction <;> rfl

theorem allocated_byte_write_protected_cancel_world (config : EvalConfig) (initialized : Nat) (owner : ActId)
    (origin : OriginId) (knownCount : Option Nat) (byte : UInt8)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout owner (.varr (.int .u8)) .value origin none knownCount before = .ok id allocated) :
    ∃ reserved written cleaned final,
      reserveExitDestination id .newValue allocated.construction = .ok (allocated.construction.exitReservations.size, id) reserved ∧
      writeElement id ⟨#[byte]⟩ reserved = .ok () written ∧
      cleanupReceivingDestination origin id [] { allocated with construction := written } = .ok () cleaned ∧
      exitChannelCleanupBorrowed origin [] [allocated.construction.exitReservations.size] true [] cleaned = .ok () final ∧
      AcceptedWorld config initialized final ambient types live regions pending := by
  obtain ⟨reserved, written, final, reserve, write, cancel, finalWorld⟩ :=
    allocated_byte_write_cancel_world config initialized owner origin knownCount byte before allocated id ambient types live regions pending world created
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
  have equivalent := protected_direct_cancel_equivalent { allocated with construction := written } origin
    allocated.construction.exitReservations.size id id 1 backing.destination nextRow nextStorage writtenTicket nextFound
    (writtenLife.1.2.1 id nextRow nextFound) (Or.inl rfl) writable nextStore nextCurrent leaf direct
  have cancelled : (do
      cancelExitReservation allocated.construction.exitReservations.size []
      releaseExitReservation allocated.construction.exitReservations.size) cleaned = .ok () final := by
    simp only [bind] at cancel ⊢
    rw [equivalent.2]
    exact cancel
  let cleanedState := { allocated with construction := cleaned }
  have cleanup : exitChannelCleanupBorrowed origin [] [allocated.construction.exitReservations.size] true [] cleanedState =
      .ok () { allocated with construction := final } := by
    have lifted : (do
        liftConstruction origin (cancelExitReservation allocated.construction.exitReservations.size [])
        liftConstruction origin (releaseExitReservation allocated.construction.exitReservations.size)) cleanedState =
          .ok () { allocated with construction := final } := by
      rw [protected_lift_sequence]
      simp [liftConstruction, cleanedState, cancelled]
    simp only [exitChannelCleanupBorrowed, Bool.true_eq, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.forIn_cons, List.forIn_nil, List.filterMap_nil, bind, pure] at lifted ⊢
    cases first : liftConstruction origin (cancelExitReservation allocated.construction.exitReservations.size []) cleanedState with
    | stop reason state | escape reason carriers state | jump reason kind state => simp [first] at lifted
    | ok value middle =>
      simp only [first] at lifted ⊢
      cases second : liftConstruction origin (releaseExitReservation allocated.construction.exitReservations.size) middle with
      | stop reason state | escape reason carriers state | jump reason kind state => simp [second] at lifted
      | ok value state =>
        simp [second] at lifted
        simp [bind, pure, first, second, lifted]
  exact ⟨expected, written, cleanedState, { allocated with construction := final }, actualReserve, write,
    equivalent.1, cleanup, finalWorld⟩

#print axioms allocated_byte_write_protected_cancel_world

end Goose.Proofs.ConstructionAcceptedExecution
