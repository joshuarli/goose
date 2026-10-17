import Goose.Proofs.ExitExecutionBase

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership

open Goose.Construct
open Goose.Core (ActId ScopeInst)
open Goose.Proofs.ExitExecution

def OwnershipBreakIdentities (state : ExecutionState) : Prop :=
  (state.breaks.map (·.id)).Nodup ∧ ∀ target ∈ state.breaks, target.id < state.nextScope

theorem OwnershipBreakIdentities.distinct {state : ExecutionState} (valid : OwnershipBreakIdentities state) :
    (state.breaks.map (·.id)).Nodup := valid.1

theorem OwnershipBreakIdentities.bounded {state : ExecutionState} (valid : OwnershipBreakIdentities state) :
    ∀ target ∈ state.breaks, target.id < state.nextScope := valid.2

structure OwnershipRuntimeIdentities (state : ExecutionState) : Prop where
  activations : FreshActivations state
  breaks : OwnershipBreakIdentities state

theorem initial_ownershipRuntimeIdentities : OwnershipRuntimeIdentities .initial :=
  ⟨freshActivations_initial, ⟨by simp [ExecutionState.initial], by simp [ExecutionState.initial]⟩⟩

theorem ownershipBreakIdentities_counter {state : ExecutionState}
    (valid : OwnershipBreakIdentities state) (counter : Nat) (grows : state.nextScope ≤ counter) :
    OwnershipBreakIdentities {state with nextScope := counter} :=
  ⟨valid.distinct, fun target member => Nat.lt_of_lt_of_le (valid.bounded target member) grows⟩

theorem ownershipRuntimeIdentities_freshAct {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) :
    OwnershipRuntimeIdentities {state with nextAct := state.nextAct + 1} :=
  ⟨preservesFresh_freshAct state valid.activations, valid.breaks⟩

theorem ownershipRuntimeIdentities_freshScope {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) :
    OwnershipRuntimeIdentities {state with nextScope := state.nextScope + 1} :=
  ⟨valid.activations, ownershipBreakIdentities_counter valid.breaks _ (Nat.le_succ _)⟩

theorem ownershipRuntimeIdentities_activation_push {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) (activation : RuntimeActivation)
    (identifier : activation.act = state.nextAct) :
    OwnershipRuntimeIdentities {state with
      nextAct := state.nextAct + 1, activations := activation :: state.activations} :=
  ⟨fresh_activation_push state activation valid.activations identifier, valid.breaks⟩

theorem ownershipBreakIdentities_push {state : ExecutionState}
    (valid : OwnershipBreakIdentities state) (act : ActId) (scope : BreakScope) (channels : List Channel) :
    let target : BreakTarget := ⟨state.nextScope, act, scope, channels⟩
    OwnershipBreakIdentities {state with nextScope := state.nextScope + 1, breaks := target :: state.breaks} := by
  refine ⟨?_, ?_⟩
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, valid.distinct⟩
    intro member
    obtain ⟨previous, member, same⟩ := List.mem_map.mp member
    have bound := valid.bounded previous member
    rw [same] at bound
    exact Nat.lt_irrefl _ bound
  · intro target member
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.lt_succ_self _
    · exact Nat.lt_trans (valid.bounded target member) (Nat.lt_succ_self _)

theorem ownershipRuntimeIdentities_break_push {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) (act : ActId) (scope : BreakScope) (channels : List Channel) :
    let target : BreakTarget := ⟨state.nextScope, act, scope, channels⟩
    OwnershipRuntimeIdentities {state with nextScope := state.nextScope + 1, breaks := target :: state.breaks} :=
  ⟨valid.activations, ownershipBreakIdentities_push valid.breaks act scope channels⟩

theorem ownershipBreakIdentities_filter {state : ExecutionState}
    (valid : OwnershipBreakIdentities state) (predicate : BreakTarget → Bool) :
    OwnershipBreakIdentities {state with breaks := state.breaks.filter predicate} := by
  refine ⟨?_, ?_⟩
  · exact List.Nodup.sublist ((List.filter_sublist (p := predicate) (l := state.breaks)).map (·.id)) valid.distinct
  · intro target member
    exact valid.bounded target (List.mem_filter.mp member).1

theorem ownershipRuntimeIdentities_filter_activation {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) (predicate : RuntimeActivation → Bool) :
    OwnershipRuntimeIdentities {state with activations := state.activations.filter predicate} :=
  ⟨fresh_activation_filter state predicate valid.activations, valid.breaks⟩

theorem ownershipRuntimeIdentities_filter_break {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) (predicate : BreakTarget → Bool) :
    OwnershipRuntimeIdentities {state with breaks := state.breaks.filter predicate} :=
  ⟨valid.activations, ownershipBreakIdentities_filter valid.breaks predicate⟩

theorem ownershipRuntimeIdentities_releaseScope {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) (environment : RuntimeActivation) (scope scopeInst : Nat) :
    OwnershipRuntimeIdentities (releaseScopeState environment scope scopeInst state) :=
  ⟨fresh_scope_release state environment scope scopeInst valid.activations, valid.breaks⟩

theorem ownershipRuntimeIdentities_afterFreshAct_push {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) (activation : RuntimeActivation)
    (identifier : activation.act = state.nextAct) :
    OwnershipRuntimeIdentities {(Goose.Proofs.Exit.stepState (freshAct state)) with
      activations := activation :: (Goose.Proofs.Exit.stepState (freshAct state)).activations} :=
  ownershipRuntimeIdentities_activation_push valid activation identifier

theorem ownershipRuntimeIdentities_afterFreshScope_push {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) (act : ActId) (scope : BreakScope) (channels : List Channel) :
    let target : BreakTarget := ⟨state.nextScope, act, scope, channels⟩
    OwnershipRuntimeIdentities {(Goose.Proofs.Exit.stepState (freshScope state)) with
      breaks := target :: (Goose.Proofs.Exit.stepState (freshScope state)).breaks} :=
  ownershipRuntimeIdentities_break_push valid act scope channels

theorem ownershipRuntimeIdentities_scopes {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) (environment : RuntimeActivation)
    (scopes : List (Nat × ScopeInst)) :
    OwnershipRuntimeIdentities {state with activations := state.activations.map (fun current =>
      if current.act == environment.act then {current with scopes := scopes} else current)} := by
  refine ⟨?_, valid.breaks⟩
  change FreshActivations (releaseScopeState {environment with scopes := scopes} 0 0 state)
  exact fresh_scope_release state {environment with scopes := scopes} 0 0 valid.activations

theorem ownershipRuntimeIdentities_resultScope {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) (environment : RuntimeActivation) (scope : Nat) :
    OwnershipRuntimeIdentities {state with
      nextScope := state.nextScope + 1, activations := state.activations.map (fun current => if current.act == environment.act then
        {current with scopes := (scope, state.nextScope) :: environment.scopes} else current)} :=
  ownershipRuntimeIdentities_scopes (ownershipRuntimeIdentities_freshScope valid) environment
    ((scope, state.nextScope) :: environment.scopes)

private theorem nodup_map_key_injective {α β : Type} (key : α → β) (items : List α)
    (distinct : (items.map key).Nodup) {left right : α}
    (leftMember : left ∈ items) (rightMember : right ∈ items) (same : key left = key right) : left = right := by
  induction items with
  | nil => cases leftMember
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp leftMember with leftHead | leftTail
    · subst left
      rcases List.mem_cons.mp rightMember with rightHead | rightTail
      · exact rightHead.symm
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨right, rightTail, same.symm⟩))
    · rcases List.mem_cons.mp rightMember with rightHead | rightTail
      · subst right
        exact False.elim (distinct.1 (List.mem_map.mpr ⟨left, leftTail, same⟩))
      · exact ih distinct.2 leftTail rightTail

theorem ownershipRuntimeIdentities_activation_unique {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) {left right : RuntimeActivation}
    (leftMember : left ∈ state.activations) (rightMember : right ∈ state.activations)
    (same : left.act = right.act) : left = right :=
  nodup_map_key_injective (·.act) state.activations valid.activations.1 leftMember rightMember same

theorem ownershipRuntimeIdentities_break_unique {state : ExecutionState}
    (valid : OwnershipRuntimeIdentities state) {left right : BreakTarget}
    (leftMember : left ∈ state.breaks) (rightMember : right ∈ state.breaks)
    (same : left.id = right.id) : left = right :=
  nodup_map_key_injective (·.id) state.breaks valid.breaks.distinct leftMember rightMember same

#print axioms ownershipRuntimeIdentities_activation_unique
#print axioms ownershipRuntimeIdentities_break_unique

end Goose.Proofs.ConstructionExecutionOwnership
