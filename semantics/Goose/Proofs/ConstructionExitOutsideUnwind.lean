import Goose.Proofs.ExitExecutionPathOutsideScopeReads
import Goose.Proofs.ConstructionExitFrameRelease

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership

private theorem valueReadBackings_all (value : Value) :
    ValueReadBackings (fun _ => True) (fun _ => True) value := by
  cases value with
  | int ty value => exact .int ty value
  | bool value => exact .bool value
  | unit => exact .unit
  | ref location => exact .ref location
  | slice location start count => exact .slice location start count
  | stored stored => exact .stored stored True.intro (fun _ _ => True.intro)
  | fixed elements =>
      apply ValueReadBackings.fixed
      intro index child found
      have inside := Array.mem_of_getElem? found
      exact valueReadBackings_all child
  | record id fields =>
      apply ValueReadBackings.record
      intro index child found
      have inside := Array.mem_of_getElem? found
      exact valueReadBackings_all child
termination_by sizeOf value

decreasing_by
  all_goals
    have smaller := Array.sizeOf_lt_of_mem inside
    simp_wf
    omega

theorem readLoc_ticket_release_observation (fuel : Nat) (layout : LayoutEnv)
    (state : ExecutionState) (token : Nat) (location : Loc) :
    let cleaned := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } }
    mapStepState (fun _ => ExecutionState.initial) (readLoc fuel layout location cleaned) =
      mapStepState (fun _ => ExecutionState.initial) (readLoc fuel layout location state) := by
  let cleaned := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token .released } }
  have frame : OutsideReadFrame state cleaned (readLoc fuel layout location) := by
    apply readLoc_outside_reads fuel layout state cleaned location rfl
    intro value present
    apply ValueReadBackings.frame (fun _ => True) (fun _ => True) state cleaned
    · intro id _; rfl
    · intro id _; rfl
    · exact valueReadBackings_all value
  exact OutsideReadResult.observation _ _ _ _ frame

theorem cleanup_two_scopes_outside_observation (fuel : Nat) (layout : LayoutEnv)
    (state : ExecutionState) (token incoming selected : Nat) (snapshot : PendingDestination)
    (origin : OriginId) (carriers : List Goose.Construct.Carrier) (inner outer : RuntimeActivation)
    (innerScope outerScope : Nat) (innerInst outerInst : ScopeInst) (location : Loc)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (outsideInner : (Goose.Proofs.Exit.runtimeScopeRoots inner innerScope innerInst).contains location.root = false)
    (outsideOuter : (Goose.Proofs.Exit.runtimeScopeRoots outer outerScope outerInst).contains location.root = false) :
    ∃ cleaned, exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () cleaned ∧
      let first := releaseScopeState inner innerScope innerInst cleaned
      let crossed := { first with activations := first.activations.filter (fun current => current.act != inner.act) }
      let second := releaseScopeState outer outerScope outerInst crossed
      let final := { second with activations := second.activations.filter (fun current => current.act != outer.act) }
      mapStepState (fun _ => ExecutionState.initial) (readLoc fuel layout location final) =
        mapStepState (fun _ => ExecutionState.initial) (readLoc fuel layout location state) := by
  let cleaned := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token .released } }
  let first := releaseScopeState inner innerScope innerInst cleaned
  let crossed := { first with activations := first.activations.filter (fun current => current.act != inner.act) }
  let second := releaseScopeState outer outerScope outerInst crossed
  let final := { second with activations := second.activations.filter (fun current => current.act != outer.act) }
  have released := releaseExitReservation_active state.construction token .fresh incoming selected snapshot ticket
  have actual : exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () cleaned := by
    simp only [exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure]
    rfl
  have outerFilter := OutsideReadResult.observation _ _ _ _
    (readLoc_construction_frame fuel layout second final location rfl rfl)
  have outerScopeRead := releaseScopeState_outside_observation fuel layout outer outerScope outerInst crossed location outsideOuter
  have innerFilter := OutsideReadResult.observation _ _ _ _
    (readLoc_construction_frame fuel layout first crossed location rfl rfl)
  have innerScopeRead := releaseScopeState_outside_observation fuel layout inner innerScope innerInst cleaned location outsideInner
  have ticketRead := readLoc_ticket_release_observation fuel layout state token location
  exact ⟨cleaned, actual, outerFilter.trans (outerScopeRead.trans (innerFilter.trans (innerScopeRead.trans ticketRead)))⟩

#print axioms readLoc_ticket_release_observation
#print axioms cleanup_two_scopes_outside_observation

end Goose.Proofs.ExitExecution
