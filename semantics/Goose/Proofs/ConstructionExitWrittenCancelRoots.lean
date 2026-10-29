import Goose.Proofs.ConstructionExitWrittenCancelFrame
import Goose.Proofs.ConstructionExitFreshCancelRoots
import Goose.Proofs.ConstructionAcceptedByteAllocation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem allocated_byte_write_cancel_frame (config : EvalConfig) (initialized : Nat) (owner : ActId)
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
      RootedBackingObservations config.layout { allocated with construction := final } live (storageExtent before) ∧
      (∀ index, index < before.construction.destinations.size →
        final.destinations[index]? = before.construction.destinations[index]?) ∧
      ∀ (index : Nat) (oldStorage : ReceivingStorage), before.construction.storage[index]? = some oldStorage →
        final.storage[index]? = some oldStorage := by
  obtain ⟨⟨backing⟩, _⟩ := newDestination_open_ready config initialized owner (.varr (.int .u8)) .value origin knownCount
    before allocated ambient types live regions pending id (.int .u8) world rfl created
  obtain ⟨newest, receiver, receiverFound, receiverUse⟩ := newDestination_newest_receiver config.layout owner (.varr (.int .u8)) .value
    origin knownCount before allocated id created
  have same : receiver = backing.destination := Option.some.inj (receiverFound.symm.trans backing.present)
  subst receiver
  obtain ⟨packedRow, packedFound, packed, _, _, _, adaptation⟩ := newDestination_byteOwner_packed_value_with_adaptation config.layout owner origin knownCount before allocated id created
  have same : packedRow = backing.destination := Option.some.inj (packedFound.symm.trans backing.present)
  subst packedRow
  have current := newDestination_current_self config initialized owner (.varr (.int .u8)) .value origin knownCount before allocated id
    ambient types live regions pending world created
  let reserved := { allocated.construction with
    exitReservations := allocated.construction.exitReservations.push (.active .fresh id id backing.destination) }
  have reserve : reserveExitDestination id .newValue allocated.construction =
      .ok (allocated.construction.exitReservations.size, id) reserved :=
    reserve_open_zero_direct allocated.construction id backing.destination backing.present backing.opened current
  have allocatedWorld := newDestination_acceptedWorld config owner (.varr (.int .u8)) .value origin knownCount initialized before allocated id
    ambient types live regions pending world created
  have lifecycle := reserveExitDestination_reservation_lifecycle id .newValue allocated.construction allocatedWorld.ownership.source.structural.1.1
  rw [reserve] at lifecycle
  have ticket : reserved.exitReservations[allocated.construction.exitReservations.size]? =
      some (.active .fresh id id backing.destination) := by simp [reserved]
  have direct : id = backing.destination.capability.id :=
    (allocatedWorld.ownership.source.structural.1.1.1.2.1 id backing.destination backing.present).symm
  have reservedCurrent : destinationCurrent reserved id = .ok id :=
    (destinationCurrent_congr_tables allocated.construction reserved rfl rfl id).trans current
  obtain ⟨written, final, write, cancel, rows, storage, tickets⟩ := direct_byte_write_cancel_frame reserved
    allocated.construction.exitReservations.size id id 0 backing.destination backing.destination backing.storage byte
    ticket backing.present backing.bytes backing.opened packed adaptation receiverUse reservedCurrent
    (by decide) newest direct lifecycle
  obtain ⟨allocation⟩ := newDestination_fresh_frame config.layout owner (.varr (.int .u8)) .value origin knownCount before allocated id
    world.ownership.source.structural.1.1.1 created
  have fresh := newDestination_fresh_id config.layout owner (.varr (.int .u8)) .value origin knownCount before allocated id created
  obtain ⟨freshRow, freshFound, freshBacking, freshStorage⟩ := newDestination_success_fresh config.layout owner (.varr (.int .u8)) .value
    origin knownCount before allocated id created
  have same : freshRow = backing.destination := Option.some.inj (freshFound.symm.trans backing.present)
  subst freshRow
  let target := { before with construction := final }
  have original := world.backing.observations config.layout before live
  have rootFrame : RootedBackingPrefixFrame before target live (storageExtent before) := by
    refine ⟨?_, ?_, ?_⟩
    · intro root retained; rfl
    · intro root retained; rfl
    · intro root retained value found stored occurrence
      have backed := (world.backing.values root retained value found).occurrence_backing config.layout before value stored occurrence
      obtain ⟨oldStorage, run, present, sampled, interval⟩ := backed.sampled config.layout before stored
      have oldInside := (Array.getElem?_eq_some_iff.mp present).1
      have different : stored.storage ≠ backing.destination.storage :=
        Nat.ne_of_lt (Nat.lt_of_lt_of_le oldInside freshStorage)
      have oldAllocated := allocation.storage stored.storage oldStorage present
      have finalStorage : final.storage[stored.storage]? = some oldStorage :=
        (storage stored.storage different).trans oldAllocated
      refine ⟨⟨oldStorage, oldStorage, present, finalStorage, ?_, rfl⟩, ?_⟩
      · simp only [storageExtent, present, Option.map_some, Option.getD_some]
        exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩
      · intro destination named
        have inside := backed.named_bound config.layout before stored destination named
        have earlier : destination < id := by simpa only [fresh] using inside
        exact (rows destination earlier).trans (allocation.lookup destination inside)
  have preserved := original.prefix_frame config.layout before target live (storageExtent before) rootFrame
  have sameTarget : { allocated with construction := final } = target := by rw [allocation.outer]
  refine ⟨reserved, written, final, reserve, write, cancel, ?_, ?_, ?_⟩
  · rw [sameTarget]
    exact preserved
  · intro index inside
    exact (rows index (by simpa only [fresh] using inside)).trans (allocation.lookup index inside)
  · intro index oldStorage present
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    have different : index ≠ backing.destination.storage := Nat.ne_of_lt (Nat.lt_of_lt_of_le inside freshStorage)
    exact (storage index different).trans (allocation.storage index oldStorage present)

theorem allocated_byte_write_cancel_rooted (config : EvalConfig) (initialized : Nat) (owner : ActId)
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
      RootedBackingObservations config.layout { allocated with construction := final } live (storageExtent before) := by
  obtain ⟨reserved, written, final, reserve, write, cancel, rooted, rows, storage⟩ :=
    allocated_byte_write_cancel_frame config initialized owner origin knownCount byte before allocated id ambient types live regions pending world created
  exact ⟨reserved, written, final, reserve, write, cancel, rooted⟩

#print axioms allocated_byte_write_cancel_frame
#print axioms allocated_byte_write_cancel_rooted

end Goose.Proofs.ConstructionAcceptedExecution
