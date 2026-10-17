import Goose.Lower.Validation.SourceSymbolRefs
import Goose.Lower.Validation.SummaryPreservationReplayTypedPlacesContracts
import Goose.Lower.Validation.SummaryPreservationReplayNativeArguments
import Goose.Lower.Validation.SummaryPreservationReplayNativeCall

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem source_argument_replay (argument : Arg) {start finish : Nat} {before after : RState}
    {roots : List RootRef}
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper)
    (source : ArgumentTyping typingEnv argument start finish)
    (replayed : ArgumentReplay env argument before roots after)
    (ceiling : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (generated : GeneratedBuilderState initial)
    (native : NativeRows vt (lowerArg argument (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2)
    (expressionChild : ∀ expression, argument = .byVal expression →
      ExpressionReplayAt typingEnv env results vt target scopeCount expression initial upper)
    (placeChild : ∀ mutability place, argument = .byRef mutability place →
      PlaceReplayAt typingEnv env results vt target scopeCount place initial upper) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerArg argument (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerArg argument (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        (lowerArg argument (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 <
          (lowerArg argument (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals.size ∧
        RootsRefine (lowerContextAt env.mod env.ctx env.impl)
          (rootsAt next.vals (lowerArg argument (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1) roots) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
  apply ready.typedArgument argument source replayed
  · intro expression type same typed replay
    have child := expressionChild expression same
    subst argument
    exact child type start finish before after roots typed replay ceiling ready generated native
  · intro mutability place info same typed replay
    have child := placeChild mutability place same
    subst argument
    let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
    let address := lowerPlace place le initial
    have placeNative : NativeRows vt address.2 :=
      native.of_prefix (types_borrowTo mutability address.1 le address.2 _ _ rfl)
    exact child info start finish before after roots typed replay ceiling ready generated placeNative

theorem expressionReplay_call {calleeId : ContextId} {args : List Arg} {origin : OriginId}
    (tables : SourceRootTables typingEnv env)
    (accepted : Core.validate env.mod = .ok ())
    (closed : ParameterRootsClosed (lowerContextAt env.mod env.ctx env.impl))
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (expressionChild : ∀ expression, Arg.byVal expression ∈ args → ∀ state provenance,
      ExpressionReplayAt typingEnv env results vt target scopeCount expression state provenance)
    (placeChild : ∀ mutability place, Arg.byRef mutability place ∈ args → ∀ state provenance,
      PlaceReplayAt typingEnv env results vt target scopeCount place state provenance) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.call calleeId args origin) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  have calleeBound : calleeId < env.mod.contexts.size := by
    simpa only [← tables.moduleEq] using Core.tyExpr_call_success_context_bound typed
  let ctx := env.mod.contexts[calleeId]'calleeBound
  have contextLookup : env.mod.contexts[calleeId]? = some ctx := Array.getElem?_eq_getElem calleeBound
  obtain ⟨callee, implLookup, _checked⟩ := (validate_modOk env.mod accepted).ctx calleeId ctx contextLookup
  have contextTyped : typingEnv.mod.contexts[calleeId]? = some ctx := by simpa only [← tables.moduleEq] using contextLookup
  have implTyped : typingEnv.mod.impls[ctx.impl]? = some callee := by simpa only [← tables.moduleEq] using implLookup
  have arity := (tyExpr_call_arguments contextTyped implTyped typed).1
  apply ready.typedCallNative tables accepted contextLookup implLookup closed bounded typed replay ceiling
    (by simpa only [lowerEnv, ← tables.moduleEq] using Core.tyExpr_call_success_origin_bound typed)
    (by simpa only [lowerEnv, Array.size_map] using calleeBound) generated native
  intro nextCounter argumentRoots sourceAfter state provenance argsTyped argsReplay argsCeiling argsReady stateEq stateGenerated argsNative
  obtain rfl := stateEq
  apply argsReady.typedArgumentsNative args callee.params.toList argsTyped (by simpa only [Array.length_toList] using arity.symm)
    _ argsReplay argsCeiling stateGenerated argsNative
  intro argument member tn1 tn2 sourceBefore childAfter childRoots childState childUpper childTyped childReplay childCeiling childReady childGenerated childNative
  apply source_argument_replay argument childReady childTyped childReplay childCeiling childGenerated childNative
  · intro expression same
    exact expressionChild expression (same ▸ member) childState childUpper
  · intro mutability place same
    exact placeChild mutability place (same ▸ member) childState childUpper

#print axioms source_argument_replay
#print axioms expressionReplay_call

end Goose.Lower.Validation.SummaryPreservation
