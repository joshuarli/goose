import Goose.Proofs.ConstructionExitActiveRestore

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

private abbrev sourceActive : PendingDestination → Bool := landing_active_source

private theorem sourceActive_matches (row : PendingDestination) : sourceActive row = activeRow row := by
  cases row.progress <;> rfl

theorem cancel_inactive_direct_saves_snapshot (state : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot selectedRow : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (selectedFound : state.destinations[selected]? = some selectedRow) (inactive : activeRow selectedRow = false)
    (direct : reserved = snapshot.capability.id) :
    cancelExitReservation token [] state = .ok () { state with
      destinationResumptions := (selected, snapshot) :: state.destinationResumptions
      exitReservations := state.exitReservations.set! token .restored } := by
  have resolvedDirect : destinationCurrent state snapshot.capability.id = .ok selected := by simpa only [direct] using resolved
  have inactiveSource : sourceActive selectedRow = false := by simpa only [sourceActive_matches] using inactive
  simp only [cancelExitReservation, ConstructionM.get, ticket, direct, resolvedDirect, bind, pure, List.any_nil,
    Bool.false_eq_true, ↓reduceIte, lookupDestination_result, selectedFound, inactiveSource,
    direct, bne_self_eq_false, ConstructionM.set]

theorem cancel_active_direct_saves_snapshot (state cleaned : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot selectedRow : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (selectedFound : state.destinations[selected]? = some selectedRow) (active : activeRow selectedRow = true)
    (tree : abandonTree selected state = .ok () cleaned) (direct : reserved = snapshot.capability.id) :
    cancelExitReservation token [] state = .ok () { cleaned with
      destinationResumptions := (selected, snapshot) :: cleaned.destinationResumptions
      exitReservations := cleaned.exitReservations.set! token .restored } := by
  have resolvedDirect : destinationCurrent state snapshot.capability.id = .ok selected := by simpa only [direct] using resolved
  have activeSource : sourceActive selectedRow = true := by simpa only [sourceActive_matches] using active
  simp only [cancelExitReservation, ConstructionM.get, ticket, direct, resolvedDirect, bind, pure, List.any_nil,
    Bool.false_eq_true, ↓reduceIte, lookupDestination_result, selectedFound, activeSource, tree,
    direct, bne_self_eq_false, ConstructionM.set]

theorem cancel_inactive_direct_preserves_child_invariants (state : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot selectedRow : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (selectedFound : state.destinations[selected]? = some selectedRow) (inactive : activeRow selectedRow = false)
    (direct : reserved = snapshot.capability.id) (unique : ActiveChildUnique state)
    (blocked : ActiveChildParentBlocked state) :
    ∃ after, cancelExitReservation token [] state = .ok () after ∧
      ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  refine ⟨_, cancel_inactive_direct_saves_snapshot state token incoming reserved selected snapshot selectedRow
    ticket resolved selectedFound inactive direct, ?_⟩
  exact ⟨unique, blocked⟩

theorem cancel_active_direct_preserves_child_invariants (state cleaned : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot selectedRow : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (selectedFound : state.destinations[selected]? = some selectedRow) (active : activeRow selectedRow = true)
    (tree : abandonTree selected state = .ok () cleaned) (direct : reserved = snapshot.capability.id)
    (indexed : DestinationCapabilitiesIndexed state) (ordered : DestinationOwnersOrdered state)
    (unique : ActiveChildUnique state) (blocked : ActiveChildParentBlocked state) :
    ∃ after, cancelExitReservation token [] state = .ok () after ∧
      ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  have candidates := abandonTree_preserves_child_invariants state cleaned selected indexed ordered unique blocked tree
  refine ⟨_, cancel_active_direct_saves_snapshot state cleaned token incoming reserved selected snapshot selectedRow
    ticket resolved selectedFound active tree direct, ?_⟩
  exact candidates

#print axioms cancel_inactive_direct_saves_snapshot
#print axioms cancel_active_direct_saves_snapshot
#print axioms cancel_inactive_direct_preserves_child_invariants
#print axioms cancel_active_direct_preserves_child_invariants

end Goose.Proofs.ConstructionAcceptedExecution
