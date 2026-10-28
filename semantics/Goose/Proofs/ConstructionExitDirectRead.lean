import Goose.Proofs.ConstructionExitDirectReturn
import Goose.Proofs.ConstructionExitByteProtectedBuild
import Goose.Proofs.ExitExecutionValuePrefixReads

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionAcceptedExecution

theorem direct_exit_outside_read (fuel : Nat) (config : EvalConfig)
    (accepted : validate config.module = .ok ()) (before after : ExecutionState)
    (retained : RootInst → Prop) (limit : Nat → Nat) (receiver : Nat)
    (valid : RootedBackingObservations config.layout before retained limit)
    (prefixes : StoragePrefixesEqual limit before.construction.storage after.construction.storage)
    (objects : ∀ root, retained root → after.objects.lookup root = before.objects.lookup root)
    (ordinals : ∀ root, retained root → after.objectOrdinals.lookup root = before.objectOrdinals.lookup root)
    (rows : ∀ id, id ≠ receiver → after.construction.destinations[id]? = before.construction.destinations[id]?)
    (names : ∀ root, retained root → ∀ value, before.objects.lookup root = some value →
      ∀ stored, StoredOccurrence value stored → stored.destination ≠ some receiver)
    (location : Loc) (outside : retained location.root) :
    mapStepState (fun _ => ExecutionState.initial) (readLoc fuel config.layout location after) =
      mapStepState (fun _ => ExecutionState.initial) (readLoc fuel config.layout location before) := by
  let bounded := fun id => min (limit id)
    ((before.construction.storage[id]?.map fun storage => storage.bytes.size).getD 0)
  have boundedValid : RootedBackingObservations config.layout before retained bounded :=
    rootedBackingObservations_bytes_bound config.layout before retained limit valid
  have frame : RootedBackingPrefixFrame before after retained bounded := by
    refine ⟨objects, ordinals, ?_⟩
    intro root kept value found stored occurrence
    have backing := (valid.backing.values root kept value found).occurrence_backing config.layout before value stored occurrence
    obtain ⟨storage, run, present, sampled, interval⟩ := backing.sampled config.layout before stored
    obtain ⟨current, currentFound, count, bytes⟩ := prefixes.lookup _ _ _ stored.storage storage present
    refine ⟨⟨storage, current, present, currentFound, ?_, count⟩, ?_⟩
    · apply BytePrefixEqual.of_extract_eq
      · simp only [bounded, present, Option.map_some, Option.getD_some]
        exact Nat.min_le_right _ _
      · have restricted := congrArg (fun data : ByteArray => data.extract 0 (bounded stored.storage)) bytes
        have boundedLimit : bounded stored.storage ≤ limit stored.storage := Nat.min_le_left _ _
        simpa only [ByteArray.extract_extract, Nat.zero_add, Nat.min_eq_left boundedLimit] using restricted
    · intro id named
      have different : id ≠ receiver := by
        intro same
        subst id
        exact names root kept value found stored occurrence named
      exact rows id different
  exact rootedBackingObservations_readLoc_observation fuel config.module accepted before after retained bounded boundedValid frame location outside

#print axioms direct_exit_outside_read

end Goose.Proofs.ExitExecution
