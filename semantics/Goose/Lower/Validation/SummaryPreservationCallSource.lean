import Goose.Lower.Validation.SummaryPreservationCallReplay

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpCall_effects {env : PEnv} {calleeId : ContextId} {ctx : Context} {callee : Impl}
    {args : List (List RootRef)} {roots : List RootRef} {before after : RState}
    (contextLookup : env.mod.contexts[calleeId]? = some ctx)
    (implLookup : env.mod.impls[ctx.impl]? = some callee)
    (replay : rpCall env calleeId args before = .ok (roots, after)) :
    after.eff = callEffects callee ctx args before.eff := by
  unfold rpCall at replay
  simp only [contextLookup, implLookup] at replay
  obtain ⟨_, middle, checked, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨_, checkedState⟩ := (liftV_ok _ _ _).mp checked
  have middleEq : middle = before := checkedState
  subst middle
  obtain ⟨_, modified, update, result⟩ := (st_bind_ok _ _ _ _).mp tail
  have updatedState := (st_modify_ok _ _ _).mp update
  have modifiedEffect : modified.eff = callEffects callee ctx args before.eff :=
    congrArg (fun pair => pair.2.eff) updatedState
  obtain ⟨_, resultState⟩ := (liftV_ok _ _ _).mp result
  have afterEq : after = modified := resultState
  rw [afterEq]
  exact modifiedEffect

theorem effectStep_call_from_source {env : PEnv} {calleeId : ContextId}
    {ctx : Context} {callee : Impl} {caller : Func} {provenance : Prov}
    {vt : Array (Option VTy)} {args : List ValueId} {sourceArgs : List (List RootRef)}
    {roots : List RootRef} {before after : RState} {result : ValueId} {origin : Option OriginId}
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[calleeId]? = some ctx)
    (implLookup : env.mod.impls[ctx.impl]? = some callee)
    (closed : ParameterRootsClosed caller)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value →
      ∃ sourceRoots, sourceArgs[index]? = some sourceRoots ∧
        RootsRepresent caller (rootsAt provenance.vals value) sourceRoots)
    (replay : rpCall env calleeId sourceArgs before = .ok (roots, after)) :
    EffectReplay caller (caller.effectStep (lower env.mod) vt provenance {}
      (.def result (.call calleeId args origin))) after.eff := by
  rw [rpCall_effects contextLookup implLookup replay]
  have lookup := lower_func_at contextLookup implLookup
  cases annotation : callee.summary with
  | unknown =>
    have loweredSummary : (lowerContextAt env.mod ctx callee).summary = .unknown := annotation
    simp only [Func.effectStep, lookup, loweredSummary, callEffects, annotation]
    constructor <;> intros <;> simp_all [Func.storageTargets]
  | known summary =>
    apply effectStep_known_call_replay lookup annotation
      ((validate_modOk env.mod accepted).impl ctx.impl callee implLookup) closed arguments
    intro index member
    exact validate_summaryTarget_bounds accepted implLookup annotation (.param index) member

end Goose.Lower.Validation.SummaryPreservation
