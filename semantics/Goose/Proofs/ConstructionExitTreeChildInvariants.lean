import Goose.Proofs.ConstructionExitProtectedChildClosure
import Goose.Proofs.ConstructionExecutionOwnershipTree

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem treeRows_active_child_closed (state : ConstructionState) (ordered : DestinationOwnersOrdered state)
    (indexed : DestinationCapabilitiesIndexed state) (root parent id : Nat)
    (owner row : PendingDestination) (ownerMember : owner ∈ treeRows state root) (ownerId : owner.capability.id = parent)
    (present : state.destinations[id]? = some row) (use : row.use = .child parent) (active : activeRow row = true) :
    row ∈ treeRows state root := by
  have ownerDescendant := ((treeRows_exact_selection state root owner).mp ownerMember).2.1
  have descendant := destinationDescendant_child state ordered root parent id row present use (by simpa only [ownerId] using ownerDescendant)
  have correct := indexed id row present
  apply (treeRows_exact_selection state root row).mpr
  exact ⟨Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨id, present⟩), by simpa only [correct] using descendant, active⟩

theorem abandonTree_preserves_child_invariants (before after : ConstructionState) (root : Nat)
    (indexed : DestinationCapabilitiesIndexed before) (ordered : DestinationOwnersOrdered before)
    (unique : ActiveChildUnique before) (blocked : ActiveChildParentBlocked before)
    (executed : abandonTree root before = .ok () after) :
    ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  classical
  have exactResult := abandonTree_success_exact before after root indexed executed
  have rowsEq : after.destinations = (abandonRowsState (treeRows before root) before).destinations := by
    rw [exactResult, treeAbandonRowsState_destinations]
  let rows := treeRows before root
  have currentRows := (treeRows_indexed before root indexed).1
  have bounded : ∀ row ∈ rows, row.capability.id < before.destinations.size := by
    intro row member
    exact (Array.getElem?_eq_some_iff.mp (currentRows row member)).1
  have distinct := (treeRows_indexed before root indexed).2
  have afterUnique := abandonRows_preserves_unique_children before rows bounded distinct unique
  constructor
  · simpa only [ActiveChildUnique, rowsEq] using afterUnique
  · intro id row owner found use active
    have foundRows : (abandonRowsState rows before).destinations[id]? = some row := by
      simpa only [rowsEq] using found
    have original := abandonRows_active_source before rows bounded distinct id row foundRows active
    obtain ⟨ownerRow, ownerFound, ownerPhase⟩ := blocked id row owner original use active
    by_cases removed : ∃ selected ∈ rows, selected.capability.id = owner
    · obtain ⟨selected, selectedMember, selectedId⟩ := removed
      have childMember : row ∈ rows := treeRows_active_child_closed before ordered indexed root owner id
        selected row selectedMember selectedId original use active
      have abandoned := abandonRowsState_inside rows before bounded distinct row childMember
      have correct := indexed id row original
      rw [correct] at abandoned
      have equal := Option.some.inj (abandoned.symm.trans foundRows)
      have phase := congrArg PendingDestination.progress equal
      have inactive : activeRow row = false := by
        cases progress : row.progress <;> simp_all [activeRow]
      rw [inactive] at active
      cases active
    · have outside : ∀ selected ∈ rows, selected.capability.id ≠ owner := by
        intro selected member equal
        exact removed ⟨selected, member, equal⟩
      refine ⟨ownerRow, ?_, ownerPhase⟩
      rw [rowsEq, abandonRowsState_outside rows before owner outside]
      exact ownerFound

#print axioms treeRows_active_child_closed
#print axioms abandonTree_preserves_child_invariants

end Goose.Proofs.ConstructionAcceptedExecution
