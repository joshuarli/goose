import Goose.Proofs.ConstructionExitRetainedCancellation
import Goose.Proofs.ConstructionExitChildWrite
import Goose.Proofs.ConstructionExecutionProtocolReservations

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

private abbrev sourceActive : PendingDestination → Bool := landing_active_source

private theorem sourceActive_matches (row : PendingDestination) : sourceActive row = activeRow row := by
  cases row.progress <;> rfl

theorem cancel_inactive_fresh_restores_snapshot (state : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot selectedRow current : PendingDestination) (count : Nat)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (selectedFound : state.destinations[selected]? = some selectedRow) (inactive : activeRow selectedRow = false)
    (different : reserved ≠ snapshot.capability.id)
    (currentFound : state.destinations[snapshot.capability.id]? = some current)
    (currentPhase : current.progress = .exiting count selected) :
    cancelExitReservation token [] state = .ok () { state with
      destinations := state.destinations.set! snapshot.capability.id snapshot
      exitReservations := state.exitReservations.set! token .restored } := by
  have currentInside := (Array.getElem?_eq_some_iff.mp currentFound).1
  have inactiveSource : sourceActive selectedRow = false := by simpa only [sourceActive_matches] using inactive
  have differentBool : (reserved != snapshot.capability.id) = true := bne_iff_ne.mpr different
  simp only [cancelExitReservation, ConstructionM.get, ticket, resolved, bind, pure, List.any_nil,
    Bool.false_eq_true, ↓reduceIte, lookupDestination_result, selectedFound, inactiveSource,
    differentBool, currentFound, currentPhase, bne_self_eq_false, replaceDestination_result,
    currentInside, ConstructionM.set]

theorem cancel_inactive_suspended_snapshot_preserves_candidates (state : ConstructionState)
    (token incoming reserved selected : Nat) (snapshot selectedRow current : PendingDestination) (count savedCount savedChild : Nat)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok selected)
    (selectedFound : state.destinations[selected]? = some selectedRow) (inactive : activeRow selectedRow = false)
    (different : reserved ≠ snapshot.capability.id)
    (currentFound : state.destinations[snapshot.capability.id]? = some current)
    (currentPhase : current.progress = .exiting count selected)
    (savedPhase : snapshot.progress = .suspended savedCount savedChild)
    (authority : FreshReservationSnapshotAuthority state)
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
  have candidates := child_invariants_replace_progress state after snapshot.capability.id current snapshot currentFound rfl use
    (by simp [activeRow, currentPhase, savedPhase]) (by simp [ChildParentPhase, currentPhase, savedPhase]) unique blocked
  exact ⟨after, actual, candidates⟩

#print axioms cancel_inactive_suspended_snapshot_preserves_candidates
#print axioms cancel_inactive_fresh_restores_snapshot

end Goose.Proofs.ConstructionAcceptedExecution
