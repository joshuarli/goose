import Goose.Proofs.OwnershipRuntimeIdentitiesChannels

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership

open Goose.Construct
open Goose.Proofs.ExitExecution

def PreservesOwnershipRuntimeIdentities (action : EvalM α) : Prop :=
  ∀ state, OwnershipRuntimeIdentities state →
    OwnershipRuntimeIdentities (Goose.Proofs.Exit.stepState (action state))

theorem preservesOwnershipRuntimeIdentities_of_components (action : EvalM α)
    (activations : PreservesFresh action) (breaks : PreservesOwnershipBreakIdentities action) :
    PreservesOwnershipRuntimeIdentities action := by
  intro state valid
  exact ⟨activations state valid.activations, breaks state valid.breaks⟩

theorem stateQuery_preservesOwnershipRuntimeIdentities (action : EvalM α) (query : StateQuery action) :
    PreservesOwnershipRuntimeIdentities action := by
  intro state valid
  rw [query state]
  exact valid

theorem preservesOwnershipRuntimeIdentities_currentBreak (act : Goose.Core.ActId) (scope : Option BreakScope) :
    PreservesOwnershipRuntimeIdentities (currentBreak act scope) :=
  stateQuery_preservesOwnershipRuntimeIdentities _ (stateQuery_currentBreak act scope)

theorem preservesOwnershipRuntimeIdentities_enclosingActivation (environment : RuntimeActivation) :
    PreservesOwnershipRuntimeIdentities (enclosingActivation environment) :=
  stateQuery_preservesOwnershipRuntimeIdentities _ (stateQuery_enclosingActivation environment)

theorem preservesOwnershipRuntimeIdentities_targetActivation (config : EvalConfig) (target : Nat) :
    PreservesOwnershipRuntimeIdentities (targetActivation config target) :=
  stateQuery_preservesOwnershipRuntimeIdentities _ (stateQuery_targetActivation config target)

theorem preservesOwnershipRuntimeIdentities_pure (value : α) :
    PreservesOwnershipRuntimeIdentities (pure value) := by intro state valid; exact valid

theorem preservesOwnershipRuntimeIdentities_stop (reason : Goose.Core.Stop) :
    PreservesOwnershipRuntimeIdentities (EvalM.stop (α := α) reason) := by intro state valid; exact valid

theorem preservesOwnershipRuntimeIdentities_get : PreservesOwnershipRuntimeIdentities EvalM.get := by
  intro state valid; exact valid

theorem preservesOwnershipRuntimeIdentities_get_bind (next : ExecutionState → EvalM α)
    (preserved : ∀ state, OwnershipRuntimeIdentities state →
      OwnershipRuntimeIdentities (Goose.Proofs.Exit.stepState (next state state))) :
    PreservesOwnershipRuntimeIdentities (EvalM.get >>= next) := preserved

theorem preservesOwnershipRuntimeIdentities_bindAll (act : Goose.Core.ActId) (scopeInst : Goose.Core.ScopeInst)
    (values : List (Goose.Core.VarId × Value)) : PreservesOwnershipRuntimeIdentities (bindAll act scopeInst values) :=
  preservesOwnershipRuntimeIdentities_of_components _ (preservesFresh_bindAll act scopeInst values)
    (preservesOwnershipBreakIdentities_bindAll act scopeInst values)

theorem preservesOwnershipRuntimeIdentities_bind (action : EvalM α) (next : α → EvalM β)
    (first : PreservesOwnershipRuntimeIdentities action)
    (remaining : ∀ value, PreservesOwnershipRuntimeIdentities (next value)) :
    PreservesOwnershipRuntimeIdentities (action >>= next) := by
  intro state valid
  have preserved := first state valid
  cases result : action state with
  | ok value final =>
    simp only [result, Goose.Proofs.Exit.stepState] at preserved
    simpa only [bind, result] using remaining value final preserved
  | stop reason final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved
  | escape target carriers final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved
  | jump target kind final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved

theorem preservesOwnershipRuntimeIdentities_lift (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    PreservesOwnershipRuntimeIdentities (liftConstruction origin action) :=
  preservesOwnershipRuntimeIdentities_of_components _ (preservesFresh_lift origin action)
    (preservesOwnershipBreakIdentities_lift origin action)

theorem preservesOwnershipRuntimeIdentities_freshAct : PreservesOwnershipRuntimeIdentities freshAct := by
  intro state valid
  exact ownershipRuntimeIdentities_freshAct valid

theorem preservesOwnershipRuntimeIdentities_freshScope : PreservesOwnershipRuntimeIdentities freshScope := by
  intro state valid
  exact ownershipRuntimeIdentities_freshScope valid

theorem preservesOwnershipRuntimeIdentities_releaseScope (environment : RuntimeActivation) (scope scopeInst : Nat) :
    PreservesOwnershipRuntimeIdentities (releaseScope environment scope scopeInst) := by
  intro state valid
  exact ownershipRuntimeIdentities_releaseScope valid environment scope scopeInst

theorem preservesOwnershipRuntimeIdentities_finishChannels (layout : LayoutEnv) (channels : List Channel)
    (types : List Ty) (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    PreservesOwnershipRuntimeIdentities (finishChannels layout channels types carriers origin) :=
  preservesOwnershipRuntimeIdentities_of_components _
    (preservesFresh_finishChannels layout channels types carriers origin)
    (preservesOwnershipBreakIdentities_finishChannels layout channels types carriers origin)

theorem preservesOwnershipRuntimeIdentities_withScope (activation : RuntimeActivation) (scope scopeInst : Nat)
    (action : EvalM α) (preserved : PreservesOwnershipRuntimeIdentities action) :
    PreservesOwnershipRuntimeIdentities (withScope activation scope scopeInst action) := by
  intro state fresh
  have after := preserved state fresh
  cases result : action state with
  | ok value final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using ownershipRuntimeIdentities_releaseScope after activation scope scopeInst
  | stop reason final =>
      simpa [withScope, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using ownershipRuntimeIdentities_releaseScope after activation scope scopeInst
  | jump target kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using ownershipRuntimeIdentities_releaseScope after activation scope scopeInst

theorem preservesOwnershipRuntimeIdentities_finishActivation (layout : LayoutEnv) (activation : RuntimeActivation)
    (types : List Ty) (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (preserved : PreservesOwnershipRuntimeIdentities action) :
    PreservesOwnershipRuntimeIdentities (finishActivation layout activation types origin action) := by
  intro state fresh
  have after := preserved state fresh
  cases result : action state with
  | ok carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      let trimmed : ExecutionState := { final with
        activations := final.activations.filter (fun current => current.act != activation.act) }
      have trimmedFresh : OwnershipRuntimeIdentities trimmed := ownershipRuntimeIdentities_filter_activation after _
      have landedFresh := preservesOwnershipRuntimeIdentities_finishChannels layout activation.channels types carriers origin trimmed trimmedFresh
      cases finished : finishChannels layout activation.channels types carriers origin trimmed <;>
        simpa [finishActivation, result, trimmed, finished, Goose.Proofs.Exit.stepState] using landedFresh
  | stop reason final =>
      simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using after
  | jump target kind final =>
      simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      by_cases caught : target.activation = activation.act
      · let trimmed : ExecutionState := { final with
          activations := final.activations.filter (fun current => current.act != activation.act) }
        have trimmedFresh : OwnershipRuntimeIdentities trimmed := ownershipRuntimeIdentities_filter_activation after _
        have landedFresh := preservesOwnershipRuntimeIdentities_finishChannels layout activation.channels types carriers origin trimmed trimmedFresh
        cases finished : finishChannels layout activation.channels types carriers origin trimmed <;>
          simpa [finishActivation, result, caught, trimmed, finished, Goose.Proofs.Exit.stepState] using landedFresh
      · simpa [finishActivation, result, caught, Goose.Proofs.Exit.stepState] using
          ownershipRuntimeIdentities_filter_activation after (fun current => current.act != activation.act)

theorem preservesOwnershipRuntimeIdentities_withBreakTarget (act : Goose.Core.ActId) (scope : BreakScope)
    (channels : List Channel) (action : EvalM α) (receive : JumpKind → EvalM α)
    (preserved : PreservesOwnershipRuntimeIdentities action)
    (received : ∀ kind, PreservesOwnershipRuntimeIdentities (receive kind)) :
    PreservesOwnershipRuntimeIdentities (withBreakTarget act scope channels action receive) := by
  intro state valid
  let target : BreakTarget := ⟨state.nextScope, act, scope, channels⟩
  let installed : ExecutionState := {state with nextScope := state.nextScope + 1, breaks := target :: state.breaks}
  have installedValid : OwnershipRuntimeIdentities installed := ownershipRuntimeIdentities_break_push valid act scope channels
  have after := preserved installed installedValid
  cases result : action installed with
  | ok value final | stop reason final | escape activation carriers final =>
    have current : OwnershipRuntimeIdentities final := by
      simpa only [result, Goose.Proofs.Exit.stepState] using after
    have removed := ownershipRuntimeIdentities_filter_break current (fun entry => entry.id != state.nextScope)
    simpa only [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState] using removed
  | jump actual kind final =>
    have current : OwnershipRuntimeIdentities final := by
      simpa only [result, Goose.Proofs.Exit.stepState] using after
    let removed : ExecutionState := {final with breaks := final.breaks.filter (fun entry => entry.id != state.nextScope)}
    have removedValid : OwnershipRuntimeIdentities removed :=
      ownershipRuntimeIdentities_filter_break current (fun entry => entry.id != state.nextScope)
    by_cases caught : actual = state.nextScope
    · simpa [withBreakTarget, installed, target, result, caught, removed, mapStepState,
        Goose.Proofs.Exit.stepState] using received kind removed removedValid
    · simpa [withBreakTarget, installed, target, result, caught, removed, mapStepState,
        Goose.Proofs.Exit.stepState] using removedValid

theorem ownershipRuntimeIdentities_withScope_stop (environment : RuntimeActivation) (scope scopeInst : Nat)
    (action : EvalM α) (state final : ExecutionState) (reason : Goose.Core.Stop)
    (stopped : action state = .stop reason final) :
    withScope environment scope scopeInst action state = .stop reason final := by
  simp only [withScope, stopped]

theorem ownershipRuntimeIdentities_finishActivation_stop (layout : LayoutEnv) (activation : RuntimeActivation)
    (types : List Ty) (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (state final : ExecutionState) (reason : Goose.Core.Stop)
    (stopped : action state = .stop reason final) :
    finishActivation layout activation types origin action state = .stop reason final := by
  simp only [finishActivation, stopped]

theorem ownershipRuntimeIdentities_withBreakTarget_stop (act : Goose.Core.ActId) (scope : BreakScope)
    (channels : List Channel) (action : EvalM α) (receive : JumpKind → EvalM α)
    (state final : ExecutionState) (reason : Goose.Core.Stop)
    (stopped : action {state with
      nextScope := state.nextScope + 1, breaks := ⟨state.nextScope, act, scope, channels⟩ :: state.breaks} = .stop reason final) :
    withBreakTarget act scope channels action receive state = .stop reason
      {final with breaks := final.breaks.filter (fun entry => entry.id != state.nextScope)} := by
  simp only [withBreakTarget, stopped, mapStepState]

theorem ownershipRuntimeIdentities_finishActivation_uncaught (layout : LayoutEnv) (activation : RuntimeActivation)
    (types : List Ty) (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (state final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : action state = .escape address carriers final) (different : address.activation ≠ activation.act) :
    finishActivation layout activation types origin action state = .escape address carriers
      {final with activations := final.activations.filter (fun current => current.act != activation.act)} := by
  simp [finishActivation, escaped, different]

theorem ownershipRuntimeIdentities_withBreakTarget_uncaught (act : Goose.Core.ActId) (scope : BreakScope)
    (channels : List Channel) (action : EvalM α) (receive : JumpKind → EvalM α)
    (state final : ExecutionState) (actual : Nat) (kind : JumpKind)
    (jumped : action {state with
      nextScope := state.nextScope + 1, breaks := ⟨state.nextScope, act, scope, channels⟩ :: state.breaks} = .jump actual kind final)
    (different : actual ≠ state.nextScope) :
    withBreakTarget act scope channels action receive state = .jump actual kind
      {final with breaks := final.breaks.filter (fun entry => entry.id != state.nextScope)} := by
  simp [withBreakTarget, jumped, mapStepState, different]

#print axioms preservesOwnershipRuntimeIdentities_finishActivation
#print axioms preservesOwnershipRuntimeIdentities_withBreakTarget

end Goose.Proofs.ConstructionExecutionOwnership
