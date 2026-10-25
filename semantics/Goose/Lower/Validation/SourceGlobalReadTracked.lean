import Goose.Lower.Validation.SourceGlobalReadPlaces
import Goose.Lower.Validation.SourceGlobalReadViews
import Goose.Lower.Validation.SourceGlobalReadReplay
import Goose.Lower.Validation.SourceGlobalReadFrames

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedGlobalPlaceTracked {typingEnv : TEnv} {env : PEnv} {place : Place}
    {info : PlaceInfo} {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (expected : List RootRef)
    (tables : SourceRootTables typingEnv env)
    (variables : typingEnv.vars = #[])
    (source : tyPlace typingEnv place start = .ok (info, finish))
    (replayed : rpPlace env place before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (ready : ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).2)
    (placeChild : ∀ owner field, place = .field owner field →
      GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount owner ls upper)
    (viewChild : ∀ view index origin, place = .elem view index origin →
      GlobalViewReplayAt typingEnv env results vt func returnTypes slots target scopeCount view ls upper)
    (expressionChild : ∀ expression state provenance,
      (place = .deref expression ∧ state = ls) ∨
        (∃ view origin, place = .elem view expression origin ∧
          state = (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).2) →
      GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression state provenance) :
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).2 next ∧
      ((lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).2.cur.isSome = true →
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).1 <
          (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).2.vals.size ∧
        RootsRefine func
          (rootsAt next.vals (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).1) sourceRoots) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved expected ls upper
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) ls).2 next := by
  obtain ⟨next, nextReady, value, retained⟩ := typedGlobalPlace tables variables source replayed wholeEffect ready generated native placeChild viewChild expressionChild
  exact ⟨next, nextReady, value, retained, ready.global_place_returns expected source retained⟩

theorem typedGlobalViewTracked {typingEnv : TEnv} {env : PEnv} {view : View} {info : Ty × Bool}
    {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (expected : List RootRef)
    (source : tyView typingEnv view start = .ok (info, finish))
    (replayed : rpView env view before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (closed : ParameterRootsClosed func)
    (ready : ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).2)
    (placeChild : ∀ place, view = .of place → GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount place ls upper)
    (expressionChild : ∀ expression, view = .val expression → GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression ls upper) :
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).2 next ∧
      ((lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).2.cur.isSome = true →
        ReplayValue func next
          (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).2
          (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).1 sourceRoots (.view .readOnly info.1)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved expected ls upper
        (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) ls).2 next := by
  obtain ⟨next, nextReady, value, retained⟩ := typedGlobalView source replayed wholeEffect closed ready generated native placeChild expressionChild
  exact ⟨next, nextReady, value, retained, ready.global_view_returns expected source retained⟩

theorem typedGlobalReadTracked {typingEnv : TEnv} {env : PEnv} {place : Place} {type : Ty}
    {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func}
    {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (expected : List RootRef)
    (checked : SourceReadableEnvironment typingEnv) (variables : typingEnv.vars = #[])
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (source : tyExpr typingEnv (.read place) start = .ok (type, finish))
    (replayed : rpExpr env (.read place) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (ready : ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars returnTypes) ls).2)
    (placeChild : GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount place ls upper) :
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots
        (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars returnTypes) ls).2 next ∧
      ((lowerExpr (.read place) (lowerEnv env.mod env.impl.vars returnTypes) ls).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars returnTypes) ls).2
          (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars returnTypes) ls).1 sourceRoots (.data type)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved expected ls upper
        (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars returnTypes) ls).2 next := by
  obtain ⟨next, nextReady, value, retained⟩ := typedGlobalRead checked variables tables closed source replayed wholeEffect ready generated native placeChild
  exact ⟨next, nextReady, value, retained, ready.global_expression_returns expected source retained⟩

#print axioms typedGlobalReadTracked
#print axioms typedGlobalPlaceTracked
#print axioms typedGlobalViewTracked

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
