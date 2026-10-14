import Goose.Construct.Eval
import Goose.Proofs.Exit

namespace Goose.Proofs.ExitExecution
open Goose.Construct

def FreshActivations (state : ExecutionState) : Prop :=
  (state.activations.map (·.act)).Nodup ∧
    ∀ activation ∈ state.activations, activation.act < state.nextAct

def PreservesFresh (action : EvalM α) : Prop :=
  ∀ state, FreshActivations state → FreshActivations (Goose.Proofs.Exit.stepState (action state))

theorem preservesFresh_pure (value : α) : PreservesFresh (pure value) := by
  intro state fresh
  exact fresh

theorem preservesFresh_stop (reason : Goose.Core.Stop) :
    PreservesFresh (EvalM.stop (α := α) reason) := by
  intro state fresh
  exact fresh

theorem preservesFresh_get : PreservesFresh EvalM.get := by
  intro state fresh
  exact fresh

theorem preservesFresh_bind (action : EvalM α) (next : α → EvalM β)
    (first : PreservesFresh action) (remaining : ∀ value, PreservesFresh (next value)) :
    PreservesFresh (action >>= next) := by
  intro state fresh
  have preserved := first state fresh
  cases result : action state with
  | ok value final =>
      simp only [result, Goose.Proofs.Exit.stepState] at preserved
      simpa only [bind, result] using remaining value final preserved
  | stop reason final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved
  | escape target carriers final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved
  | jump target kind final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved

theorem preservesFresh_lift (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    PreservesFresh (liftConstruction origin action) := by
  intro state fresh
  unfold liftConstruction
  cases action state.construction <;> exact fresh

theorem freshActivations_initial : FreshActivations .initial := by
  simp [FreshActivations, ExecutionState.initial]

theorem freshAct_result (state : ExecutionState) :
    freshAct state = .ok state.nextAct { state with nextAct := state.nextAct + 1 } := rfl

theorem preservesFresh_freshAct : PreservesFresh freshAct := by
  intro state fresh
  rw [freshAct_result]
  obtain ⟨distinct, earlier⟩ := fresh
  refine ⟨distinct, ?_⟩
  intro activation member
  exact Nat.lt_trans (earlier activation member) (Nat.lt_succ_self _)

theorem preservesFresh_freshScope : PreservesFresh freshScope := by
  intro state fresh
  exact fresh

theorem preservesFresh_returned (activation : Goose.Core.ActId) (carriers : List Carrier) :
    PreservesFresh (returned (α := α) activation carriers) := by
  intro state fresh
  exact fresh

theorem targetActivation_selects_nearest (config : EvalConfig) (targetId : Nat)
    (state final : ExecutionState) (activation : RuntimeActivation)
    (selected : targetActivation config targetId state = .ok activation final) :
    final = state ∧ ∃ target discarded outer,
      config.module.targets[targetId]? = some target ∧
      state.activations = discarded ++ activation :: outer ∧
      target.contains activation.implementation = true ∧
      ∀ earlier ∈ discarded, target.contains earlier.implementation = false := by
  cases targetFound : config.module.targets[targetId]? with
  | none => simp [targetActivation, targetFound, fault, EvalM.stop] at selected
  | some target =>
      cases activationFound : selectTarget? target state.activations with
      | none =>
          simp [targetActivation, targetFound, activationFound, EvalM.get, fault, EvalM.stop, bind] at selected
      | some catcher =>
          simp [targetActivation, targetFound, activationFound, EvalM.get, bind, pure] at selected
          obtain ⟨equal, unchanged⟩ := selected
          subst catcher
          subst final
          obtain ⟨discarded, outer, shape, membership, excluded⟩ :=
            Goose.Proofs.Exit.runtime_select_nearest target state.activations activation activationFound
          exact ⟨rfl, target, discarded, outer, rfl, shape, membership, excluded⟩

theorem fresh_activation_push (state : ExecutionState) (activation : RuntimeActivation)
    (fresh : FreshActivations state) (identifier : activation.act = state.nextAct) :
    FreshActivations { state with
      nextAct := state.nextAct + 1, activations := activation :: state.activations } := by
  obtain ⟨distinct, earlier⟩ := fresh
  constructor
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, distinct⟩
    intro member
    obtain ⟨previous, member, equal⟩ := List.mem_map.mp member
    have smaller := earlier previous member
    rw [equal, identifier] at smaller
    exact Nat.lt_irrefl _ smaller
  · intro current member
    rcases List.mem_cons.mp member with equal | member
    · subst current
      rw [identifier]
      exact Nat.lt_succ_self _
    · exact Nat.lt_trans (earlier current member) (Nat.lt_succ_self _)

theorem fresh_scope_release (state : ExecutionState) (activation : RuntimeActivation)
    (scope scopeInst : Nat) (fresh : FreshActivations state) :
    FreshActivations (releaseScopeState activation scope scopeInst state) := by
  obtain ⟨distinct, earlier⟩ := fresh
  have same : ((releaseScopeState activation scope scopeInst state).activations.map (·.act)) =
      state.activations.map (·.act) := by
    simp [releaseScopeState, List.map_map]
    intro current _
    split <;> rfl
  refine ⟨by rw [same]; exact distinct, ?_⟩
  intro current member
  have mapped : current.act ∈ (releaseScopeState activation scope scopeInst state).activations.map (·.act) :=
    List.mem_map.mpr ⟨current, member, rfl⟩
  rw [same] at mapped
  obtain ⟨previous, member, equal⟩ := List.mem_map.mp mapped
  simpa [releaseScopeState, equal] using earlier previous member

theorem preservesFresh_withScope (activation : RuntimeActivation) (scope scopeInst : Nat)
    (action : EvalM α) (preserved : PreservesFresh action) :
    PreservesFresh (withScope activation scope scopeInst action) := by
  intro state fresh
  have after := preserved state fresh
  cases result : action state with
  | ok value final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using fresh_scope_release final activation scope scopeInst after
  | stop reason final =>
      simpa [withScope, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using fresh_scope_release final activation scope scopeInst after
  | jump target kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using fresh_scope_release final activation scope scopeInst after

end Goose.Proofs.ExitExecution
