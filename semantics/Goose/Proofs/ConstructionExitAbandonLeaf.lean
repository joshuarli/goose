import Goose.Proofs.ConstructionExitAbandonOlder

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem abandon_leaf_success (state : ConstructionState) (id count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage)
    (present : state.destinations[id]? = some row) (identity : row.capability.id = id)
    (phase : row.progress = .open count ∨ row.progress = .built count)
    (writable : destinationCanWrite state id = true)
    (stored : state.storage[row.storage]? = some storage)
    (leaf : treeRows state id = [row]) :
    abandonTree id state = .ok () (abandonRowState state id row storage) := by
  have current : state.destinations[row.capability.id]? = some row := by simpa only [identity] using present
  have step : treeCleanupStep row state = .ok () (abandonRowState state id row storage) := by
    rw [treeCleanupStep_current_equation row state current, identity, writable]
    simp only [↓reduceIte]
    rcases phase with phase | phase
    all_goals
      simp only [phase]
      exact abandonDestination_exact state id row storage present writable ⟨count, by simp [phase]⟩ stored
  rw [abandonTree_cleanup_equation, present, writable]
  rcases phase with phase | phase
  all_goals
    simp [phase, leaf, treeHasExiting, treeCleanupLoop, step, bind, pure]

theorem cancel_active_leaf_preserves_older (state : ConstructionState)
    (token incoming reserved selected count : Nat) (snapshot row : PendingDestination) (storage : ReceivingStorage)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (present : state.destinations[selected]? = some row) (identity : row.capability.id = selected)
    (phase : row.progress = .open count ∨ row.progress = .built count)
    (writable : destinationCanWrite state selected = true)
    (stored : state.storage[row.storage]? = some storage)
    (leaf : treeRows state selected = [row]) (direct : reserved = snapshot.capability.id)
    (lifecycle : ReservationLifecycleInvariant state) :
    ∃ final, (do cancelExitReservation token []; releaseExitReservation token) state = .ok () final ∧
      (∀ index, index < selected → final.destinations[index]? = state.destinations[index]?) ∧
      (∀ other, other ≠ token → final.exitReservations[other]? = state.exitReservations[other]?) := by
  have active : activeRow row = true := by
    rcases phase with phase | phase <;> simp [activeRow, phase]
  exact cancel_active_direct_preserves_older state (abandonRowState state selected row storage)
    token incoming reserved selected snapshot row ticket resolved present active
    (abandon_leaf_success state selected count row storage present identity phase writable stored leaf) direct lifecycle

#print axioms abandon_leaf_success
#print axioms cancel_active_leaf_preserves_older

end Goose.Proofs.ConstructionAcceptedExecution
