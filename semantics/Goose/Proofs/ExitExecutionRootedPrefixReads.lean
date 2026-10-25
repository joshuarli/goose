import Goose.Proofs.ConstructionRootedBackingPrefixes
import Goose.Proofs.ExitExecutionStoredPrefixReads

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation

theorem storedBackingObservation_readStoredElement_observation (fuel : Nat) (module : Module)
    (accepted : validate module = .ok ()) (before after : ExecutionState) (limit : Nat → Nat)
    (stored : StoredValue) (index : Nat)
    (observed : StoredBackingObservation (.ofModule module) before limit stored)
    (frame : StoredBackingPrefixFrame before after limit stored) :
    mapStepState (fun _ => ExecutionState.initial)
        (readStoredElement fuel (.ofModule module) stored index after) =
      mapStepState (fun _ => ExecutionState.initial)
        (readStoredElement fuel (.ofModule module) stored index before) := by
  obtain ⟨storage, run, backingFuel, finish, present, sampled, measured, lower, upper⟩ := observed.observed
  obtain ⟨original, current, originalFound, currentFound, bytes, published⟩ := frame.storage
  have same := Option.some.inj (originalFound.symm.trans present)
  subst original
  have transported := sampledStored_storage_transport stored before after storage current run
    present currentFound published frame.destination sampled
  have originalRun : storedPathRun stored before =
      .ok (storage.bytes, storedWrittenRun stored run) before := by
    simp only [storedPathRun, sampled, bind, pure]
    rfl
  have currentRun : storedPathRun stored after =
      .ok (current.bytes, storedWrittenRun stored run) after := by
    simp only [storedPathRun, transported, bind, pure]
    rfl
  exact readStoredElement_prefix_observation fuel backingFuel (.ofModule module)
    (validated_fixedLayoutFieldBounds module accepted) stored index before after storage.bytes current.bytes
    (storedWrittenRun stored run) finish originalRun currentRun measured (bytes.restrict finish upper)

theorem rootedBackingObservations_storedElement_observation (fuel : Nat) (module : Module)
    (accepted : validate module = .ok ()) (before after : ExecutionState)
    (retainedRoot : Goose.Core.RootInst → Prop) (limit : Nat → Nat)
    (valid : RootedBackingObservations (.ofModule module) before retainedRoot limit)
    (frame : RootedBackingPrefixFrame before after retainedRoot limit)
    (root : Goose.Core.RootInst) (retained : retainedRoot root) (value : Value)
    (present : before.objects.lookup root = some value) (stored : StoredValue)
    (occurrence : StoredOccurrence value stored) (index : Nat) :
    mapStepState (fun _ => ExecutionState.initial)
        (readStoredElement fuel (.ofModule module) stored index after) =
      mapStepState (fun _ => ExecutionState.initial)
        (readStoredElement fuel (.ofModule module) stored index before) :=
  storedBackingObservation_readStoredElement_observation fuel module accepted before after limit stored index
    (valid.observations root retained value present stored occurrence)
    (frame.sources root retained value present stored occurrence)

#print axioms storedBackingObservation_readStoredElement_observation
#print axioms rootedBackingObservations_storedElement_observation

end Goose.Proofs.ExitExecution
