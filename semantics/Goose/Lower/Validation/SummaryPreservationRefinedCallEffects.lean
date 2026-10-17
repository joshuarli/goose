import Goose.Lower.Validation.SummaryPreservationRefinedCallTargets
import Goose.Lower.Validation.SummaryPreservationCallSource

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem effectStep_known_call_refines {module : GIR.Module} {sourceModule : Core.Module}
    {caller : Func} {callee : Impl} {ctx : Context} {provenance : Prov}
    {vt : Array (Option VTy)} {calleeId : FnId} {args : List ValueId}
    {sourceArgs : List (List RootRef)} {before : Core.Eff} {summary : Core.Summary}
    {result : ValueId} {origin : Option OriginId}
    (lookup : module.funcs[calleeId]? = some (lowerContextAt sourceModule ctx callee))
    (known : callee.summary = .known summary) (calleeOk : Core.Sound.ImplOk sourceModule callee)
    (closed : ParameterRootsClosed caller)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value →
      ∃ sourceRoots, sourceArgs[index]? = some sourceRoots ∧
        RootsRefine caller (rootsAt provenance.vals value) sourceRoots)
    (bounds : ∀ index, Target.param index ∈ summary.reads ++ summary.writes ++ summary.grows ++
      summary.shrinks ++ summary.rebinds → index < callee.params.size) :
    EffectRefinement caller (caller.effectStep module vt provenance {} (.def result (.call calleeId args origin)))
      (callEffects callee ctx sourceArgs before) := by
  let expanded := args.map fun value =>
    ((rootsAt provenance.vals value).flatMap caller.expandParameterRoot).foldl
      (fun acc root => unionRoots acc [root]) []
  have argumentBounds := expandedCallArguments_storage_refines closed arguments
  have mapped (targets : List Target)
      (targetBounds : ∀ index, Target.param index ∈ targets → index < callee.params.size) :
      ∀ target ∈ caller.storageTargets (addTargets [] (addTargets (mapSummaryTargets expanded targets)
        (targets.flatMap fun
          | .param index =>
            match (lowerContextAt sourceModule ctx callee).params[index]? with
            | some ty => if ty.isRefLike then
                (((lowerContextAt sourceModule ctx callee).roots.params.find? (·.1 == index)).map (·.2)).getD []
                  |>.filterMap fun | .global global => some (Target.global global) | _ => none
              else []
            | none => []
          | .global _ => []))), target ∈ caller.storageTargets (mapCallTargets callee ctx sourceArgs targets) := by
    intro target member
    rcases storageTargets_addTargets_origin member with empty | actual
    · simp [Func.storageTargets] at empty
    · have transported := congrArg
        (fun globals : List Target => target ∈ caller.storageTargets
          (addTargets (mapSummaryTargets expanded targets) globals))
        (lowerContextAt_callGlobals (ctx := ctx) calleeOk targets targetBounds)
      exact mapCallTargets_storage_refines argumentBounds targets target (Eq.mp transported actual)
  have calleeSummary : (lowerContextAt sourceModule ctx callee).summary = callee.summary := rfl
  simp only [Func.effectStep, lookup, calleeSummary, known, callEffects]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro target member
    apply storageTargets_mono (fun t h => Core.Sound.addTargets_right _ _ t h)
    exact mapped summary.reads (fun index member => bounds index (by simp [member])) target member
  · intro target member
    apply storageTargets_mono (fun t h => Core.Sound.addTargets_right _ _ t h)
    exact mapped summary.writes (fun index member => bounds index (by simp [member])) target member
  · intro target member
    apply storageTargets_mono (fun t h => Core.Sound.addTargets_right _ _ t h)
    exact mapped summary.grows (fun index member => bounds index (by simp [member])) target member
  · intro target member
    apply storageTargets_mono (fun t h => Core.Sound.addTargets_right _ _ t h)
    exact mapped summary.shrinks (fun index member => bounds index (by simp [member])) target member
  · intro target member
    simp at member
  · intro aborts
    simp only [Bool.false_or] at aborts
    simp only [Bool.or_eq_true]
    exact Or.inr aborts
  · intro outputs
    simp only [Bool.false_or] at outputs
    simp only [Bool.or_eq_true]
    exact Or.inr outputs
  · intro unknown
    cases unknown

theorem effectStep_call_refines_from_source {env : PEnv} {calleeId : ContextId}
    {ctx : Context} {callee : Impl} {caller : Func} {provenance : Prov}
    {vt : Array (Option VTy)} {args : List ValueId} {sourceArgs : List (List RootRef)}
    {roots : List RootRef} {before after : RState} {result : ValueId} {origin : Option OriginId}
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[calleeId]? = some ctx)
    (implLookup : env.mod.impls[ctx.impl]? = some callee)
    (closed : ParameterRootsClosed caller)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value →
      ∃ sourceRoots, sourceArgs[index]? = some sourceRoots ∧
        RootsRefine caller (rootsAt provenance.vals value) sourceRoots)
    (replay : rpCall env calleeId sourceArgs before = .ok (roots, after)) :
    EffectRefinement caller (caller.effectStep (lower env.mod) vt provenance {}
      (.def result (.call calleeId args origin))) after.eff := by
  rw [rpCall_effects contextLookup implLookup replay]
  have lookup := lower_func_at contextLookup implLookup
  cases annotation : callee.summary with
  | unknown =>
    have loweredSummary : (lowerContextAt env.mod ctx callee).summary = .unknown := annotation
    simp only [Func.effectStep, lookup, loweredSummary, callEffects, annotation]
    constructor <;> intros <;> simp_all [Func.storageTargets]
  | known summary =>
    apply effectStep_known_call_refines lookup annotation
      ((validate_modOk env.mod accepted).impl ctx.impl callee implLookup) closed arguments
    intro index member
    exact validate_summaryTarget_bounds accepted implLookup annotation (.param index) member

end Goose.Lower.Validation.SummaryPreservation
