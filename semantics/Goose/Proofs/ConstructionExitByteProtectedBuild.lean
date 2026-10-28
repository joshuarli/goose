import Goose.Proofs.ConstructionExitByteProtection
import Goose.Proofs.ConstructionExitByteFinishPrefix
import Goose.Proofs.ExitExecutionAcceptedLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem rootedBackingObservations_storagePrefixes (layout : LayoutEnv) (before after : ExecutionState)
    (retained : Goose.Core.RootInst → Prop) (limit : Nat → Nat)
    (valid : RootedBackingObservations layout before retained limit)
    (prefixes : StoragePrefixesEqual limit before.construction.storage after.construction.storage)
    (objects : after.objects = before.objects) (ordinals : after.objectOrdinals = before.objectOrdinals)
    (rows : ∀ root, retained root → ∀ value, before.objects.lookup root = some value →
      ∀ stored, StoredOccurrence value stored → ∀ id, stored.destination = some id →
      after.construction.destinations[id]? = before.construction.destinations[id]?) :
    RootedBackingObservations layout after retained limit := by
  let bounded := fun id => min (limit id)
    ((before.construction.storage[id]?.map fun storage => storage.bytes.size).getD 0)
  have boundedValid : RootedBackingObservations layout before retained bounded :=
    rootedBackingObservations_bytes_bound layout before retained limit valid
  have frame : RootedBackingPrefixFrame before after retained bounded := by
    refine ⟨fun _ _ => by rw [objects], fun _ _ => by rw [ordinals], ?_⟩
    intro root kept value found stored occurrence
    have backing := (valid.backing.values root kept value found).occurrence_backing layout before value stored occurrence
    obtain ⟨storage, run, present, sampled, interval⟩ := backing.sampled layout before stored
    obtain ⟨current, currentFound, count, bytes⟩ := prefixes.lookup _ _ _ stored.storage storage present
    refine ⟨⟨storage, current, present, currentFound, ?_, count⟩, rows root kept value found stored occurrence⟩
    apply BytePrefixEqual.of_extract_eq
    · simp only [bounded, present, Option.map_some, Option.getD_some]
      exact Nat.min_le_right _ _
    · have restricted := congrArg (fun data : ByteArray => data.extract 0 (bounded stored.storage)) bytes
      have boundedLimit : bounded stored.storage ≤ limit stored.storage := Nat.min_le_left _ _
      simpa only [ByteArray.extract_extract, Nat.zero_add, Nat.min_eq_left boundedLimit] using restricted
  have moved := boundedValid.prefix_frame layout before after retained bounded frame
  refine ⟨moved.backing, ?_⟩
  intro root kept value found stored occurrence
  obtain ⟨storage, run, fuel, finish, present, sampled, measured, lower, upper⟩ :=
    (moved.observations root kept value found stored occurrence).observed
  exact ⟨storage, run, fuel, finish, present, sampled, measured, lower,
    Nat.le_trans upper (Nat.min_le_left _ _)⟩

theorem packed_byte_build_protection (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count : Nat) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (liveRoots : Goose.Core.RootInst → Prop) (region : ReceivingRegion)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (different : region.destination ≠ id) (mutable : id ∈ region.mutableDestinations)
    (cutoff : region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (protection : ReceivingProtection config.layout before liveRoots region)
    (built : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    ReceivingProtection config.layout after liveRoots region := by
  obtain ⟨present, cutoff', landing, authority, authorityBound, names⟩ :=
    packed_byte_build_protection_metadata fuel config environment id count bytes origin before after
      liveRoots region valid ready packed request current different protection built
  have prefixes := build_packed_byte_storage_prefix fuel config environment id count bytes origin
    before after region.limit valid ready packed request cutoff current built
  have runtime := buildExpr_bytes_runtime fuel config environment id _ bytes origin before after
    ready.destination count valid current ready.present ready.opened built
  have objects := congrArg ExecutionState.objects runtime
  have ordinals := congrArg ExecutionState.objectOrdinals runtime
  refine ⟨present, ?_, cutoff', landing, authority, authorityBound, names⟩
  apply rootedBackingObservations_storagePrefixes config.layout before after _ region.limit protection.observations prefixes objects ordinals
  intro root kept value found stored occurrence selected destination
  have nonmember := protection.names root kept.1 kept.2 value found stored occurrence selected destination
  have distinct : selected ≠ id := by
    intro equal
    subst selected
    exact nonmember mutable
  exact build_packed_bytes_other_row fuel config environment id count selected bytes origin before after
    valid ready packed request current distinct built

#print axioms rootedBackingObservations_storagePrefixes
#print axioms packed_byte_build_protection

end Goose.Proofs.ConstructionAcceptedExecution
