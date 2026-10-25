import Goose.Proofs.ExitExecutionValuePrefixReads
import Goose.Proofs.ExitExecutionCleanupStorageObservations

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation

private def storageEnd (state : ExecutionState) (id : Nat) : Nat :=
  (state.construction.storage[id]?.map fun storage => storage.bytes.size).getD 0

theorem storedBackingObservation_bytes_bound (layout : LayoutEnv) (state : ExecutionState)
    (limit : Nat → Nat) (stored : StoredValue)
    (observed : StoredBackingObservation layout state limit stored)
    (backed : StoredValueBacking layout state stored) :
    StoredBackingObservation layout state (fun id => min (limit id) (storageEnd state id)) stored := by
  obtain ⟨storage, run, fuel, finish, present, sampled, measured, lower, upper⟩ := observed.observed
  obtain ⟨original, originalRun, originalFound, originalSampled, originalBacking⟩ := backed.sampled layout state stored
  have storageSame := Option.some.inj (originalFound.symm.trans present)
  subst original
  have runSame : originalRun = run := by
    exact congrArg Prod.snd (ExecutionStep.ok.inj (originalSampled.symm.trans sampled)).1
  subst originalRun
  obtain ⟨backingFuel, backingEnd, backingMeasured, backingLower, backingUpper⟩ := originalBacking.interval
  have finishSame := elementsEnd_success_unique fuel backingFuel layout run.element
    (storedWrittenRun stored run).count storage.bytes run.byteStart finish backingEnd measured backingMeasured
  refine ⟨storage, run, fuel, finish, present, sampled, measured, lower, Nat.le_min.mpr ⟨upper, ?_⟩⟩
  simp only [storageEnd, present, Option.map_some, Option.getD_some]
  omega

theorem rootedBackingObservations_bytes_bound (layout : LayoutEnv) (state : ExecutionState)
    (retainedRoot : Goose.Core.RootInst → Prop) (limit : Nat → Nat)
    (valid : RootedBackingObservations layout state retainedRoot limit) :
    RootedBackingObservations layout state retainedRoot
      (fun id => min (limit id) (storageEnd state id)) := by
  refine ⟨valid.backing, ?_⟩
  intro root retained value present stored occurrence
  exact storedBackingObservation_bytes_bound layout state limit stored
    (valid.observations root retained value present stored occurrence)
    ((valid.backing.values root retained value present).occurrence_backing layout state value stored occurrence)

theorem cleanupStorageTrace_rooted_read_observation (fuel : Nat) (module : Module)
    (accepted : validate module = .ok ()) (before after : ExecutionState)
    (retainedRoot : Goose.Core.RootInst → Prop) (limit : Nat → Nat)
    (valid : RootedBackingObservations (.ofModule module) before retainedRoot limit)
    (cuts : List CleanupStorageBoundary)
    (trace : CleanupStorageTrace cuts before.construction.storage after.construction.storage)
    (geometry : ∀ cut ∈ cuts, limit cut.storage ≤ cut.retainedEnd)
    (objects : ∀ root, retainedRoot root → after.objects.lookup root = before.objects.lookup root)
    (destinations : ∀ root, retainedRoot root → ∀ value, before.objects.lookup root = some value →
      ∀ stored, StoredOccurrence value stored → ∀ id, stored.destination = some id →
        after.construction.destinations[id]? = before.construction.destinations[id]?)
    (location : Goose.Core.Loc) (retained : retainedRoot location.root) :
    mapStepState (fun _ => ExecutionState.initial) (readLoc fuel (.ofModule module) location after) =
      mapStepState (fun _ => ExecutionState.initial) (readLoc fuel (.ofModule module) location before) := by
  let bounded := fun id => min (limit id) (storageEnd before id)
  have boundedGeometry : ∀ cut ∈ cuts, bounded cut.storage ≤ cut.retainedEnd := by
    intro cut member
    exact Nat.le_trans (Nat.min_le_left _ _) (geometry cut member)
  have prefixes : StoragePrefixesEqual bounded before.construction.storage after.construction.storage :=
    trace.prefixes bounded boundedGeometry
  have boundedValid := rootedBackingObservations_bytes_bound (.ofModule module) before retainedRoot limit valid
  apply readLoc_prefix_observation fuel module accepted before after bounded location (objects location.root retained)
  intro value found stored occurrence
  refine ⟨boundedValid.observations location.root retained value found stored occurrence, ?_⟩
  have backed := (valid.backing.values location.root retained value found).occurrence_backing (.ofModule module) before value stored occurrence
  obtain ⟨storage, run, present, sampled, interval⟩ := backed.sampled (.ofModule module) before stored
  obtain ⟨current, currentFound, count, bytes⟩ := prefixes.lookup _ _ _ stored.storage storage present
  refine ⟨⟨storage, current, present, currentFound, ?_, count⟩,
    destinations location.root retained value found stored occurrence⟩
  apply BytePrefixEqual.of_extract_eq
  · simp only [bounded, storageEnd, present, Option.map_some, Option.getD_some]
    exact Nat.min_le_right _ _
  · exact bytes

#print axioms storedBackingObservation_bytes_bound
#print axioms rootedBackingObservations_bytes_bound
#print axioms cleanupStorageTrace_rooted_read_observation

end Goose.Proofs.ExitExecution
