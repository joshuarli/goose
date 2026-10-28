import Goose.Proofs.ConstructionExitByteCapability
import Goose.Proofs.ConstructionExitByteAdaptation
import Goose.Proofs.ConstructionExitByteNormalize
import Goose.Proofs.ConstructionAcceptedBytePublication

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

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
