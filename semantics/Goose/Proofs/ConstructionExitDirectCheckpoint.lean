import Goose.Proofs.ConstructionExitDirectRead
import Goose.Proofs.ConstructionExitValidatedNonempty
import Goose.Proofs.ConstructionExecutionProtocolLifecycle

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecutionChecks

def recursiveDirectCheckpoint : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 28 ⟨.release, recursiveDestinations⟩ .initial)

theorem recursive_checkpoint_reservation_lifecycle :
    ReservationLifecycleInvariant recursiveDirectCheckpoint.construction := by
  letI := reservationLifecyclePrimitives
  letI := reservationLifecycleReservationPrimitives
  exact runModule_preservesConstructionInvariant (predicate := ReservationLifecycleInvariant)
    28 ⟨.release, recursiveDestinations⟩ .initial initial_reservation_lifecycle_invariant

theorem recursive_checkpoint_destination_lifecycle :
    DestinationLifecycleInvariant recursiveDirectCheckpoint.construction :=
  recursive_checkpoint_reservation_lifecycle.1

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem recursive_checkpoint_open_indexed_receiver :
    ∃ row, recursiveDirectCheckpoint.construction.destinations[1]? = some row ∧
      row.progress = .open 0 ∧ row.capability.id = 1 := by
  have phase : recursiveDirectCheckpoint.construction.destinations[1]?.map (·.progress) = some (.open 0) := by
    cbv
  cases present : recursiveDirectCheckpoint.construction.destinations[1]? with
  | none => simp [present] at phase
  | some row =>
    have opened : row.progress = .open 0 := by simpa [present] using phase
    exact ⟨row, rfl, opened, recursive_checkpoint_destination_lifecycle.2.1 1 row present⟩

theorem protection_excludes_mutable_receiver (layout : LayoutEnv) (state : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion) (id : Nat)
    (protection : ReceivingProtection layout state live region)
    (authority : id ∈ region.mutableDestinations) :
    ∀ root, (live root ∧ ¬ region.mutableRoots root) → ∀ value,
      state.objects.lookup root = some value → ∀ stored, StoredOccurrence value stored → stored.destination ≠ some id := by
  intro root retained value present stored occurrence named
  exact (protection.names root retained.1 retained.2 value present stored occurrence id named) authority

#print axioms recursive_checkpoint_reservation_lifecycle
#print axioms recursive_checkpoint_destination_lifecycle
#print axioms recursive_checkpoint_open_indexed_receiver
#print axioms protection_excludes_mutable_receiver

end Goose.Proofs.ConstructionAcceptedExecution
