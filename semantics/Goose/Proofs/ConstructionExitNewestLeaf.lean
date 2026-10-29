import Goose.Proofs.ConstructionExitAbandonLeaf
import Goose.Proofs.ConstructionExitByteNormalize

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

private theorem unique_rows_singleton (rows : List PendingDestination) (row : PendingDestination)
    (member : row ∈ rows) (unique : rows.Pairwise (fun a b => a.capability.id ≠ b.capability.id))
    (same : ∀ other ∈ rows, other = row) : rows = [row] := by
  cases rows with
  | nil => simp at member
  | cons first rest =>
    have firstEq := same first (by simp)
    subst first
    have absent := (List.pairwise_cons.mp unique).1 row
    have empty : rest = [] := by
      cases rest with
      | nil => rfl
      | cons other tail =>
        have eq := same other (by simp)
        subst other
        exact False.elim (absent (by simp) rfl)
    simp [empty]

theorem newest_active_destination_is_leaf (state : ConstructionState) (id : Nat) (row : PendingDestination)
    (present : state.destinations[id]? = some row) (active : activeRow row = true)
    (newest : state.destinations.size = id + 1)
    (indexed : DestinationCapabilitiesIndexed state) (ordered : DestinationOwnersOrdered state) :
    treeRows state id = [row] := by
  have identity := indexed id row present
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have member : row ∈ treeRows state id := by
    apply (treeRows_exact_selection state id row).mpr
    refine ⟨?_, ?_, active⟩
    · apply Array.mem_toList_iff.mpr
      exact Array.mem_iff_getElem?.mpr ⟨id, present⟩
    · simpa only [identity] using destinationDescendant_self state id inside
  apply unique_rows_singleton _ row member (treeRows_indexed state id indexed).2
  intro other kept
  have found := (treeRows_indexed state id indexed).1 other kept
  have bound := (Array.getElem?_eq_some_iff.mp found).1
  have descendant := ((treeRows_exact_selection state id other).mp kept).2.1
  have le : other.capability.id ≤ id := Nat.lt_succ_iff.mp (by simpa only [newest] using bound)
  have equal : other.capability.id = id := by
    by_cases same : other.capability.id = id
    · exact same
    · have earlier : other.capability.id < id := Nat.lt_of_le_of_ne le same
      have absent := destinationDescendant_false_of_lt state ordered id other.capability.id earlier
      rw [absent] at descendant
      contradiction
  rw [equal, present] at found
  exact (Option.some.inj found).symm

theorem cancel_newest_direct_receiver_preserves_older (state : ConstructionState)
    (token incoming reserved selected count : Nat) (snapshot row : PendingDestination) (storage : ReceivingStorage)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (present : state.destinations[selected]? = some row) (use : row.use = .receiver)
    (phase : row.progress = .open count ∨ row.progress = .built count)
    (stored : state.storage[row.storage]? = some storage)
    (newest : state.destinations.size = selected + 1) (direct : reserved = snapshot.capability.id)
    (lifecycle : ReservationLifecycleInvariant state) :
    ∃ final, (do cancelExitReservation token []; releaseExitReservation token) state = .ok () final ∧
      (∀ index, index < selected → final.destinations[index]? = state.destinations[index]?) ∧
      (∀ other, other ≠ token → final.exitReservations[other]? = state.exitReservations[other]?) := by
  have active : activeRow row = true := by
    rcases phase with phase | phase <;> simp [activeRow, phase]
  have leaf := newest_active_destination_is_leaf state selected row present active newest lifecycle.1.2.1 lifecycle.1.2.2.2
  exact cancel_active_leaf_preserves_older state token incoming reserved selected count snapshot row storage
    ticket resolved present (lifecycle.1.2.1 selected row present) phase
    (Goose.Proofs.ExitExecution.receiver_destination_writable state selected row present use) stored leaf direct lifecycle

#print axioms newest_active_destination_is_leaf
#print axioms cancel_newest_direct_receiver_preserves_older

end Goose.Proofs.ConstructionAcceptedExecution
