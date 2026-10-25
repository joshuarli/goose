import Goose.Proofs.ExitExecutionCompletedBacking
import Goose.Proofs.ExitExecutionCleanupRootedObservations

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership

theorem completedStep_rooted_observations (module : Module) (accepted : validate module = .ok ())
    (origin : Goose.Core.OriginId) (before : ExecutionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (Goose.Core.DestinationId × PendingDestination)) (stored : StoredValue)
    (retainedRoot : Goose.Core.RootInst → Prop) (limit : Nat → Nat)
    (indexed : DestinationCapabilitiesIndexed before.construction)
    (backed : StoredValueBacking (.ofModule module) before stored) (named : stored.destination = some id)
    (present : before.construction.destinations[id]? = some replacement)
    (storedLookup : before.construction.storage[replacement.storage]? = some storage)
    (built : replacement.progress = .built count)
    (sameStorage : superseded.storage = replacement.storage)
    (ordered : superseded.capability.start ≤ replacement.capability.start)
    (parentBound : ∀ parentId parent, parentUpdate = some (parentId, parent) → parentId < before.construction.destinations.size)
    (parentDifferent : ∀ parentId parent, parentUpdate = some (parentId, parent) → parentId ≠ id)
    (valid : RootedBackingObservations (.ofModule module) before retainedRoot limit)
    (geometry : limit replacement.storage ≤ superseded.capability.start)
    (outsideDestinations : ∀ root, retainedRoot root → ∀ value, before.objects.lookup root = some value →
      ∀ source, StoredOccurrence value source → ∀ destination, source.destination = some destination →
        id ≠ destination ∧
        (∀ row ∈ protectedRows before.construction old id, row.capability.id ≠ destination) ∧
        (∀ parentId parent, parentUpdate = some (parentId, parent) → parentId ≠ destination)) :
    let after : ExecutionState := { before with construction := completedLandingState before.construction id old count replacement superseded storage parentUpdate }
    liftConstruction origin (completedStep id old count replacement superseded parentUpdate) before = .ok () after ∧
      after.construction.stdout = before.construction.stdout ∧
      stored.storage = superseded.storage ∧
      StoredValueBacking (.ofModule module) after { stored with start := superseded.capability.start } ∧
      ∀ fuel location, retainedRoot location.root →
        mapStepState (fun _ => ExecutionState.initial) (readLoc fuel (.ofModule module) location after) =
          mapStepState (fun _ => ExecutionState.initial) (readLoc fuel (.ofModule module) location before) := by
  let after : ExecutionState := { before with construction := completedLandingState before.construction id old count replacement superseded storage parentUpdate }
  obtain ⟨success, identity, transported⟩ := completedStep_named_backing (.ofModule module) origin before id old count
    replacement superseded storage parentUpdate stored indexed backed named present storedLookup built
    sameStorage ordered parentBound parentDifferent
  refine ⟨success, completedLandingState_stdout before.construction id old count replacement superseded storage parentUpdate,
    identity, transported, ?_⟩
  have sourceInside := storedValueBacking_named_start_bound (.ofModule module) before id count replacement storage stored
    backed named present storedLookup built
  have protectedBytes := landingBytes_prefix storage.bytes superseded.capability.start replacement.capability.start ordered sourceInside
  have trace : CleanupStorageTrace [⟨replacement.storage, superseded.capability.start⟩]
      before.construction.storage after.construction.storage := by
    change CleanupStorageTrace _ _ (completedLandingState before.construction id old count replacement superseded storage parentUpdate).storage
    rw [completedLandingState_storage]
    exact .rewrite before.construction.storage replacement.storage storage
      (storage.landExit superseded.capability.start replacement.capability.start) superseded.capability.start
      storedLookup rfl protectedBytes.bytes
  have cutGeometry : ∀ (cut : CleanupStorageBoundary), cut ∈ [⟨replacement.storage, superseded.capability.start⟩] → limit cut.storage ≤ cut.retainedEnd := by
    intro cut member
    simp only [List.mem_singleton] at member
    cases member
    exact geometry
  intro fuel location retained
  apply cleanupStorageTrace_rooted_read_observation fuel module accepted before after retainedRoot limit valid
    [⟨replacement.storage, superseded.capability.start⟩] trace cutGeometry (fun _ _ => rfl) _ location retained
  intro root kept value found source occurrence destination selected
  obtain ⟨different, rows, parent⟩ := outsideDestinations root kept value found source occurrence destination selected
  exact completedLandingState_outside_destination before.construction id old count replacement superseded storage
    parentUpdate destination different rows parent

#print axioms completedStep_rooted_observations

end Goose.Proofs.ExitExecution
