import Goose.Proofs.ConstructionExitByteFinishParent
import Goose.Proofs.ConstructionExitByteCaptured
import Goose.Proofs.ConstructionExitByteRuntime
import Goose.Proofs.ConstructionAcceptedState

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem packed_byte_build_protection_metadata (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count : Nat) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (liveRoots : Goose.Core.RootInst → Prop) (region : ReceivingRegion)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (different : region.destination ≠ id)
    (protection : ReceivingProtection config.layout before liveRoots region)
    (built : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    (∃ row, after.construction.destinations[region.destination]? = some row) ∧
    (∀ row, after.construction.destinations[region.destination]? = some row →
      region.limit row.storage ≤ row.rollbackEnd) ∧
    (∀ row, after.construction.destinations[region.destination]? = some row →
      region.limit row.storage ≤ row.capability.start) ∧
    region.destination ∈ region.mutableDestinations ∧
    (∀ other ∈ region.mutableDestinations, other < after.construction.destinations.size) ∧
    (∀ root, liveRoots root → ¬ region.mutableRoots root → ∀ value,
      after.objects.lookup root = some value → ∀ stored, StoredOccurrence value stored →
      ∀ other, stored.destination = some other → other ∉ region.mutableDestinations) := by
  have row := build_packed_bytes_other_row fuel config environment id count region.destination bytes origin
    before after valid ready packed request current different built
  have size := (build_packed_bytes_indexing fuel config environment id count bytes origin
    before after valid ready packed request current built).1
  have runtime := buildExpr_bytes_runtime fuel config environment id _ bytes origin before after
    ready.destination count valid current ready.present ready.opened built
  refine ⟨?_, ?_, ?_, protection.authority, ?_, ?_⟩
  · simpa only [row] using protection.present
  · intro destination present
    exact protection.cutoff destination (by simpa only [row] using present)
  · intro destination present
    exact protection.landing destination (by simpa only [row] using present)
  · intro other member
    rw [size]
    exact protection.authorityBound other member
  · intro root live immutable value present stored occurrence other destination
    apply protection.names root live immutable value _ stored occurrence other destination
    have objects := congrArg ExecutionState.objects runtime
    simpa only [objects] using present

#print axioms packed_byte_build_protection_metadata

end Goose.Proofs.ConstructionAcceptedExecution
