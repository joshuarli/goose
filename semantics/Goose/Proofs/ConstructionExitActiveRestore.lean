import Goose.Proofs.ConstructionExitTreeChildInvariants
import Goose.Proofs.ConstructionExitInactiveRestore

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

private abbrev sourceActive : PendingDestination → Bool := landing_active_source

private theorem sourceActive_matches (row : PendingDestination) : sourceActive row = activeRow row := by
  cases row.progress <;> rfl

theorem abandonTree_success_earlier_row (state after : ConstructionState) (root index : Nat)
    (indexed : DestinationCapabilitiesIndexed state) (ordered : DestinationOwnersOrdered state)
    (earlier : index < root) (executed : abandonTree root state = .ok () after) :
    after.destinations[index]? = state.destinations[index]? := by
  apply abandonTree_success_outside state after root index indexed executed
  intro row member equal
  have descendant := ((treeRows_exact_selection state root row).mp member).2.1
  have absent := destinationDescendant_false_of_lt state ordered root index earlier
  rw [equal, absent] at descendant
  cases descendant

theorem cancel_active_fresh_restores_snapshot (state cleaned : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot selectedRow current : PendingDestination) (count : Nat)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (selectedFound : state.destinations[selected]? = some selectedRow) (active : activeRow selectedRow = true)
    (tree : abandonTree selected state = .ok () cleaned) (different : reserved ≠ snapshot.capability.id)
    (currentFound : cleaned.destinations[snapshot.capability.id]? = some current)
    (currentPhase : current.progress = .exiting count selected) :
    cancelExitReservation token [] state = .ok () { cleaned with
      destinations := cleaned.destinations.set! snapshot.capability.id snapshot
      exitReservations := cleaned.exitReservations.set! token .restored } := by
  have currentInside := (Array.getElem?_eq_some_iff.mp currentFound).1
  have activeSource : sourceActive selectedRow = true := by simpa only [sourceActive_matches] using active
  have differentBool : (reserved != snapshot.capability.id) = true := bne_iff_ne.mpr different
  simp only [cancelExitReservation, ConstructionM.get, ticket, resolved, bind, pure, List.any_nil,
    Bool.false_eq_true, ↓reduceIte, lookupDestination_result, selectedFound, activeSource, tree,
    differentBool, currentFound, currentPhase, bne_self_eq_false, replaceDestination_result,
    currentInside, ConstructionM.set]

theorem cancel_active_suspended_snapshot_preserves_candidates (state cleaned : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot selectedRow current : PendingDestination) (count savedCount savedChild : Nat)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (selectedFound : state.destinations[selected]? = some selectedRow) (active : activeRow selectedRow = true)
    (tree : abandonTree selected state = .ok () cleaned) (different : reserved ≠ snapshot.capability.id)
    (currentFound : state.destinations[snapshot.capability.id]? = some current)
    (currentPhase : current.progress = .exiting count selected)
    (savedPhase : snapshot.progress = .suspended savedCount savedChild)
    (lifecycle : ReservationLifecycleInvariant state) (authority : FreshReservationSnapshotAuthority state)
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
  let after := { cleaned with
    destinations := cleaned.destinations.set! snapshot.capability.id snapshot
    exitReservations := cleaned.exitReservations.set! token .restored }
  have actual : cancelExitReservation token [] state = .ok () after :=
    cancel_active_fresh_restores_snapshot state cleaned token incoming reserved selected snapshot selectedRow current count
      ticket resolved selectedFound active tree different currentClean currentPhase
  have candidates := child_invariants_replace_progress cleaned after snapshot.capability.id current snapshot currentClean rfl use
    (by simp [activeRow, currentPhase, savedPhase]) (by simp [ChildParentPhase, currentPhase, savedPhase])
    cleanedCandidates.1 cleanedCandidates.2
  exact ⟨after, actual, candidates⟩

#print axioms cancel_active_suspended_snapshot_preserves_candidates
#print axioms abandonTree_success_earlier_row
#print axioms cancel_active_fresh_restores_snapshot

end Goose.Proofs.ConstructionAcceptedExecution
