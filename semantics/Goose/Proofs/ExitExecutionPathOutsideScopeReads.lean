import Goose.Proofs.ExitExecutionPathOutsideReads

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core

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

theorem readLoc_construction_frame (fuel : Nat) (layout : LayoutEnv)
    (before after : ExecutionState) (location : Loc)
    (root : after.objects.lookup location.root = before.objects.lookup location.root)
    (construction : after.construction = before.construction) :
    OutsideReadFrame before after (Goose.Construct.readLoc fuel layout location) := by
  apply readLoc_outside_reads fuel layout before after location root
  intro value present
  apply ValueReadBackings.frame (fun _ => True) (fun _ => True) before after
  · intro id _
    rw [construction]
  · intro id _
    rw [construction]
  · exact valueReadBackings_all value

private theorem scope_filter_lookup (roots : List RootInst) (entries : List (RootInst × Value))
    (root : RootInst) (outside : roots.contains root = false) :
    (entries.filter (fun entry => !roots.contains entry.1)).lookup root = entries.lookup root := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases same : key = root
      · subst key
        simp only [List.filter, List.lookup, outside, Bool.not_false, beq_self_eq_true]
      · have mismatch : (root == key) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
        cases kept : roots.contains key <;>
          simp only [List.filter, List.lookup, kept, Bool.not_false, Bool.not_true, mismatch, ih]

theorem releaseScopeState_root_lookup (environment : RuntimeActivation) (scope scopeInst : Nat)
    (state : ExecutionState) (root : RootInst)
    (outside : (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains root = false) :
    (releaseScopeState environment scope scopeInst state).objects.lookup root = state.objects.lookup root :=
  scope_filter_lookup _ _ _ outside

theorem releaseScopeState_outside_read (fuel : Nat) (layout : LayoutEnv)
    (environment : RuntimeActivation) (scope scopeInst : Nat) (state : ExecutionState) (location : Loc)
    (outside : (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains location.root = false) :
    OutsideReadFrame state (releaseScopeState environment scope scopeInst state)
      (Goose.Construct.readLoc fuel layout location) := by
  apply readLoc_construction_frame fuel layout state _ location
  · exact scope_filter_lookup _ _ _ outside
  · exact Goose.Proofs.Exit.runtime_release_scope_construction environment scope scopeInst state

theorem releaseScopeState_outside_observation (fuel : Nat) (layout : LayoutEnv)
    (environment : RuntimeActivation) (scope scopeInst : Nat) (state : ExecutionState) (location : Loc)
    (outside : (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains location.root = false) :
    mapStepState (fun _ => ExecutionState.initial)
        (Goose.Construct.readLoc fuel layout location (releaseScopeState environment scope scopeInst state)) =
      mapStepState (fun _ => ExecutionState.initial) (Goose.Construct.readLoc fuel layout location state) :=
  OutsideReadResult.observation _ _ _ _
    (releaseScopeState_outside_read fuel layout environment scope scopeInst state location outside)

end Goose.Proofs.ExitExecution
