import Goose.Proofs.ConstructionExitProtectionPath
import Goose.Proofs.ConstructionAcceptedByteSource

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem reserved_byte_landing_old_rows (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (before after : ExecutionState) (reserved : ConstructionState)
    (incoming selected token count writeCount : Nat) (bytes : List UInt8) (origin : OriginId)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (receiverCurrent : destinationCurrent before.construction incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (valid : OwnershipSourceState reserved)
    (ready : OpenDestinationBacking config.layout { before with construction := reserved } selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent reserved selected = .ok selected)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin)
      { before with construction := reserved } = .ok () after) :
    ∀ row ∈ protectedRows after.construction incoming selected,
      row.capability.id < before.construction.destinations.size ∧
      (row.capability.id ≠ incoming → before.construction.destinations[row.capability.id]? = some row) := by
  have source := buildExpr_bytes_sourceState fuel config environment selected (.varr (.int .u8)) bytes origin
    { before with construction := reserved } after ready.destination writeCount valid current ready.present ready.opened built
  have indexed : DestinationCapabilitiesIndexed after.construction := source.structural.1.1.1.2.1
  have size := (build_packed_bytes_indexing fuel config environment selected writeCount bytes origin
    { before with construction := reserved } after valid ready packed request current built).1
  change after.construction.destinations.size = reserved.destinations.size at size
  have reservationFrame := reserve_open_other_rows before.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes receiverCurrent reservation
  have fresh := reserve_open_replacement_fresh before.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes receiverCurrent reservation
  intro row member
  have inside := (protectedRows_indexed after.construction incoming selected indexed).1 row member
  have ne := ((protectedRows_exact_selection after.construction incoming selected row).mp member).2.1
  have old : row.capability.id < before.construction.destinations.size := by
    rw [size, reservationFrame.1] at inside
    rw [fresh] at ne
    exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp inside) ne
  refine ⟨old, ?_⟩
  intro notReceiver
  obtain ⟨index, found⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp
    ((protectedRows_exact_selection after.construction incoming selected row).mp member).1)
  have correct := indexed index row found
  have foundId : after.construction.destinations[row.capability.id]? = some row := by simpa only [correct] using found
  have buildRow := build_packed_bytes_other_row fuel config environment selected writeCount row.capability.id bytes origin
    { before with construction := reserved } after valid ready packed request current ne built
  have oldRow := reservationFrame.2 row.capability.id notReceiver old
  rw [buildRow, oldRow] at foundId
  exact foundId

theorem reserved_byte_landing_authority (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (before after : ExecutionState) (reserved : ConstructionState)
    (incoming selected token count writeCount : Nat) (bytes : List UInt8) (origin : OriginId)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (receiverCurrent : destinationCurrent before.construction incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (valid : OwnershipSourceState reserved)
    (ready : OpenDestinationBacking config.layout { before with construction := reserved } selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent reserved selected = .ok selected)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin)
      { before with construction := reserved } = .ok () after)
    (region : ReceivingRegion) (destination : region.destination = incoming)
    (receiverAuthority : region.destination ∈ region.mutableDestinations)
    (activeAuthority : ∀ (id : Nat) (row : PendingDestination), before.construction.destinations[id]? = some row → activeRow row = true →
      row.capability.id ∈ region.mutableDestinations) :
    ∀ row ∈ protectedRows after.construction incoming selected,
      row.capability.id ∈ (selected :: region.mutableDestinations) := by
  have frame := reserved_byte_landing_old_rows fuel config environment before after reserved incoming selected token
    count writeCount bytes origin receiver receiverCurrent reservation valid ready packed request current built
  intro row member
  have old := frame row member
  have active := ((protectedRows_exact_selection after.construction incoming selected row).mp member).2.2.2
  simp only [List.mem_cons]
  right
  by_cases receiverRow : row.capability.id = incoming
  · simpa only [receiverRow, ← destination] using receiverAuthority
  · exact activeAuthority row.capability.id row (old.2 receiverRow) active

#print axioms reserved_byte_landing_authority
#print axioms reserved_byte_landing_old_rows

end Goose.Proofs.ConstructionAcceptedExecution
