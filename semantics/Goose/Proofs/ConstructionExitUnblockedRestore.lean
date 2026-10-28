import Goose.Proofs.ConstructionExitInactiveRestore
import Goose.Proofs.ConstructionExitActiveRestore

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

def NoActiveChildren (state : ConstructionState) (parent : Nat) : Prop :=
  ∀ (id : Nat) (row : PendingDestination), state.destinations[id]? = some row →
    row.use = .child parent → activeRow row = true → False

theorem child_invariants_replace_without_children (before after : ConstructionState) (id : Nat)
    (old new : PendingDestination) (present : before.destinations[id]? = some old)
    (rows : after.destinations = before.destinations.set! id new)
    (sameUse : new.use = old.use) (sameActive : activeRow new = activeRow old)
    (noChildren : NoActiveChildren before id)
    (unique : ActiveChildUnique before) (blocked : ActiveChildParentBlocked before) :
    ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have outside : ∀ other, other ≠ id → after.destinations[other]? = before.destinations[other]? := by
    intro other distinct
    rw [rows]
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm distinct]
  have current : after.destinations[id]? = some new := by
    rw [rows]
    simp [Array.set!_eq_setIfInBounds, inside]
  have recover : ∀ (index : Nat) (row : PendingDestination) (owner : Nat),
      after.destinations[index]? = some row → row.use = .child owner → activeRow row = true →
      ∃ original, before.destinations[index]? = some original ∧ original.use = .child owner ∧ activeRow original = true := by
    intro index row owner found use active
    by_cases same : index = id
    · subst index
      have equal := Option.some.inj (current.symm.trans found)
      subst row
      exact ⟨old, present, sameUse.symm.trans use, sameActive.symm.trans active⟩
    · exact ⟨row, by rw [← outside index same]; exact found, use, active⟩
  constructor
  · intro owner first second left right leftFound leftUse leftActive rightFound rightUse rightActive
    obtain ⟨oldLeft, leftBefore, leftChild, leftWasActive⟩ := recover first left owner leftFound leftUse leftActive
    obtain ⟨oldRight, rightBefore, rightChild, rightWasActive⟩ := recover second right owner rightFound rightUse rightActive
    exact unique owner first second oldLeft oldRight leftBefore leftChild leftWasActive rightBefore rightChild rightWasActive
  · intro index row owner found use active
    obtain ⟨original, originalFound, originalUse, originalActive⟩ := recover index row owner found use active
    by_cases same : owner = id
    · subst owner
      exact False.elim (noChildren index original originalFound originalUse originalActive)
    · obtain ⟨parent, parentFound, phase⟩ := blocked index original owner originalFound originalUse originalActive
      exact ⟨parent, by rw [outside owner same]; exact parentFound, phase⟩

theorem cancel_inactive_unblocked_snapshot_preserves_candidates (state : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot selectedRow current : PendingDestination) (count : Nat)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (selectedFound : state.destinations[selected]? = some selectedRow) (inactive : activeRow selectedRow = false)
    (different : reserved ≠ snapshot.capability.id)
    (currentFound : state.destinations[snapshot.capability.id]? = some current)
    (currentPhase : current.progress = .exiting count selected)
    (savedPhase : ∃ savedCount, snapshot.progress = .open savedCount ∨ snapshot.progress = .built savedCount)
    (authority : FreshReservationSnapshotAuthority state)
    (noChildren : NoActiveChildren state snapshot.capability.id)
    (unique : ActiveChildUnique state) (blocked : ActiveChildParentBlocked state) :
    ∃ after, cancelExitReservation token [] state = .ok () after ∧
      ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  have snapshotSame := authority token incoming reserved snapshot current ticket different currentFound count selected currentPhase
  have use : snapshot.use = current.use := (congrArg PendingDestination.use snapshotSame).symm
  let after := { state with
    destinations := state.destinations.set! snapshot.capability.id snapshot
    exitReservations := state.exitReservations.set! token .restored }
  have actual : cancelExitReservation token [] state = .ok () after :=
    cancel_inactive_fresh_restores_snapshot state token incoming reserved selected snapshot selectedRow current count
      ticket resolved selectedFound inactive different currentFound currentPhase
  have active : activeRow snapshot = activeRow current := by
    obtain ⟨savedCount, phase | phase⟩ := savedPhase <;> simp [activeRow, phase, currentPhase]
  have candidates := child_invariants_replace_without_children state after snapshot.capability.id current snapshot currentFound rfl use
    active noChildren unique blocked
  exact ⟨after, actual, candidates⟩

theorem cancel_active_unblocked_snapshot_preserves_candidates (state cleaned : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot selectedRow current : PendingDestination) (count : Nat)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (selectedFound : state.destinations[selected]? = some selectedRow) (active : activeRow selectedRow = true)
    (tree : abandonTree selected state = .ok () cleaned) (different : reserved ≠ snapshot.capability.id)
    (currentFound : state.destinations[snapshot.capability.id]? = some current)
    (currentPhase : current.progress = .exiting count selected)
    (savedPhase : ∃ savedCount, snapshot.progress = .open savedCount ∨ snapshot.progress = .built savedCount)
    (lifecycle : ReservationLifecycleInvariant state) (authority : FreshReservationSnapshotAuthority state)
    (noChildren : NoActiveChildren state snapshot.capability.id)
    (unique : ActiveChildUnique state) (blocked : ActiveChildParentBlocked state) :
    ∃ after, cancelExitReservation token [] state = .ok () after ∧
      ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  have prior : snapshot.capability.id ≤ reserved := (lifecycle.2.active token .fresh incoming reserved snapshot ticket).2.2.1
  have strict : snapshot.capability.id < reserved := Nat.lt_of_le_of_ne prior (Ne.symm different)
  have earlier : snapshot.capability.id < selected := Nat.lt_of_lt_of_le strict (destinationCurrent_bounds state reserved selected resolved).1
  have sameRow := abandonTree_success_earlier_row state cleaned selected snapshot.capability.id lifecycle.1.2.1 lifecycle.1.2.2.2 earlier tree
  have currentClean : cleaned.destinations[snapshot.capability.id]? = some current := sameRow.trans currentFound
  have snapshotSame := authority token incoming reserved snapshot current ticket different currentFound count selected currentPhase
  have use : snapshot.use = current.use := (congrArg PendingDestination.use snapshotSame).symm
  have cleanedCandidates := abandonTree_preserves_child_invariants state cleaned selected lifecycle.1.2.1 lifecycle.1.2.2.2 unique blocked tree
  have noCleanChildren : NoActiveChildren cleaned snapshot.capability.id := by
    intro id row found child activeRowProof
    have exactState := abandonTree_success_exact state cleaned selected lifecycle.1.2.1 tree
    have rowsEq : cleaned.destinations = (abandonRowsState (treeRows state selected) state).destinations := by
      rw [exactState, treeAbandonRowsState_destinations]
    have currentRows := (treeRows_indexed state selected lifecycle.1.2.1).1
    have bounded : ∀ member ∈ treeRows state selected, member.capability.id < state.destinations.size := by
      intro member included
      exact (Array.getElem?_eq_some_iff.mp (currentRows member included)).1
    have oldFound := abandonRows_active_source state (treeRows state selected) bounded
      (treeRows_indexed state selected lifecycle.1.2.1).2 id row (by simpa only [rowsEq] using found) activeRowProof
    exact noChildren id row oldFound child activeRowProof
  let after := { cleaned with
    destinations := cleaned.destinations.set! snapshot.capability.id snapshot
    exitReservations := cleaned.exitReservations.set! token .restored }
  have actual : cancelExitReservation token [] state = .ok () after :=
    cancel_active_fresh_restores_snapshot state cleaned token incoming reserved selected snapshot selectedRow current count
      ticket resolved selectedFound active tree different currentClean currentPhase
  have sameActive : activeRow snapshot = activeRow current := by
    obtain ⟨savedCount, phase | phase⟩ := savedPhase <;> simp [activeRow, phase, currentPhase]
  have candidates := child_invariants_replace_without_children cleaned after snapshot.capability.id current snapshot currentClean rfl use
    sameActive noCleanChildren cleanedCandidates.1 cleanedCandidates.2
  exact ⟨after, actual, candidates⟩

#print axioms cancel_active_unblocked_snapshot_preserves_candidates
#print axioms child_invariants_replace_without_children
#print axioms cancel_inactive_unblocked_snapshot_preserves_candidates

end Goose.Proofs.ConstructionAcceptedExecution
