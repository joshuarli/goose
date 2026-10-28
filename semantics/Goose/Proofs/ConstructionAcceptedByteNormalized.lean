import Goose.Proofs.ConstructionExitByteCapability
import Goose.Proofs.ConstructionExitByteAdaptation
import Goose.Proofs.ConstructionExitByteNormalize
import Goose.Proofs.ConstructionAcceptedBytePublication

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

structure BuiltByteReceiver (layout : LayoutEnv) (state : ExecutionState) (id storageId count : Nat) where
  row : PendingDestination
  storage : ReceivingStorage
  present : state.construction.destinations[id]? = some row
  stored : state.construction.storage[storageId]? = some storage
  progress : row.progress = .built count
  receiver : row.use = .receiver
  backing : row.backing = .direct storageId
  storageEq : row.storage = storageId
  packed : row.layout = .packed
  request : row.capability.request = .value
  logical : row.capability.logicalType = .varr (.int .u8)
  adaptation : row.adaptation = none
  sampled : SampledRunBacking layout storage.bytes ⟨row.capability.start + 4, count, .int .u8⟩
  normalized : NormalizedCompletedCarrier state (.varr (.int .u8)) id

def BuiltByteReceiver.of_construction_eq {before after : ExecutionState} {layout : LayoutEnv} {id storageId count : Nat}
    (same : after.construction = before.construction) (facts : BuiltByteReceiver layout before id storageId count) :
    BuiltByteReceiver layout after id storageId count where
  row := facts.row
  storage := facts.storage
  present := by rw [same]; exact facts.present
  stored := by rw [same]; exact facts.stored
  progress := facts.progress
  receiver := facts.receiver
  backing := facts.backing
  storageEq := facts.storageEq
  packed := facts.packed
  request := facts.request
  logical := facts.logical
  adaptation := facts.adaptation
  sampled := facts.sampled
  normalized := facts.normalized.of_construction_eq same

theorem packed_byte_build_receiver (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id storageId : Nat) (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (receiver : ready.destination.use = .receiver) (adaptation : ready.destination.adaptation = none)
    (physical : ready.destination.capability.layout = .varr (.int .u8))
    (direct : ready.destination.backing = .direct storageId)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (built : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    Nonempty (BuiltByteReceiver config.layout after id storageId bytes.length) := by
  obtain ⟨row, storage, found, stored, layout, mode, logical, backing, use, progress, sampled⟩ :=
    buildExpr_byteOwner_geometry fuel config environment bytes origin id 0 before after ready packed request
      (by simpa using fits) valid.structural.1.1.1 current built
  obtain ⟨capRow, capFound, capability, capProgress⟩ :=
    build_packed_bytes_capability fuel config environment id 0 bytes origin before after valid ready packed request current built
  have sameCap : capRow = row := Option.some.inj (capFound.symm.trans found)
  subst capRow
  obtain ⟨adaptRow, adaptFound, adapted, adaptProgress⟩ :=
    build_packed_bytes_adaptation fuel config environment id 0 bytes origin before after valid ready packed request current built
  have sameAdapt : adaptRow = row := Option.some.inj (adaptFound.symm.trans found)
  subst adaptRow
  have actualReceiver : row.use = .receiver := use.trans receiver
  have actualPhysical : row.capability.layout = .varr (.int .u8) := by rw [capability, physical]
  have actualBacking : row.backing = .direct storageId := backing.trans direct
  have storageEq : row.storage = storageId := by
    simp [PendingDestination.storage, actualBacking, DestinationBacking.writeStorage]
  have normalized : NormalizedCompletedCarrier after (.varr (.int .u8)) id := by
    refine ⟨row, found, ⟨0 + bytes.length, progress⟩,
      receiver_destination_writable after.construction id row found actualReceiver, adapted.trans adaptation, ?_, logical, rfl⟩
    simp only [actualPhysical, Bool.not_true, Bool.and_false]
  refine ⟨⟨row, storage, found, ?_, by simpa using progress, actualReceiver, actualBacking, storageEq,
    layout, mode, logical, adapted.trans adaptation, by simpa using sampled, normalized⟩⟩
  simpa only [storageEq] using stored

#print axioms packed_byte_build_receiver
theorem packed_byte_build_normalized (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Nat) (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (receiver : ready.destination.use = .receiver) (adaptation : ready.destination.adaptation = none)
    (physical : ready.destination.capability.layout = .varr (.int .u8))
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (built : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    Nonempty (NormalizedCompletedCarrier after (.varr (.int .u8)) id) := by
  obtain ⟨row, storage, found, stored, layout, mode, logical, backing, use, progress, sampled⟩ :=
    buildExpr_byteOwner_geometry fuel config environment bytes origin id 0 before after ready packed request
      (by simpa using fits) valid.structural.1.1.1 current built
  obtain ⟨capRow, capFound, capability, capProgress⟩ :=
    build_packed_bytes_capability fuel config environment id 0 bytes origin before after valid ready packed request current built
  have sameCap : capRow = row := Option.some.inj (capFound.symm.trans found)
  subst capRow
  obtain ⟨adaptRow, adaptFound, adapted, adaptProgress⟩ :=
    build_packed_bytes_adaptation fuel config environment id 0 bytes origin before after valid ready packed request current built
  have sameAdapt : adaptRow = row := Option.some.inj (adaptFound.symm.trans found)
  subst adaptRow
  have actualReceiver : row.use = .receiver := use.trans receiver
  have actualPhysical : row.capability.layout = .varr (.int .u8) := by rw [capability, physical]
  refine ⟨⟨row, found, ⟨0 + bytes.length, progress⟩,
    receiver_destination_writable after.construction id row found actualReceiver, adapted.trans adaptation, ?_, logical, rfl⟩⟩
  simp only [actualPhysical, Bool.not_true, Bool.and_false]

#print axioms packed_byte_build_normalized
end Goose.Proofs.ConstructionAcceptedExecution
