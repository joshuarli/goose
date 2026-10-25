import Goose.Lower.Validation.SourceGlobalReadPlaces
import Goose.Lower.Validation.SourceGlobalReadViews
import Goose.Lower.Validation.SourceGlobalReadReplay
import Goose.Lower.Validation.SourceGlobalReadFrames

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedInitializerPlace {env : PEnv} {module : Core.Module} {global : Core.Global} {globalId : GlobalId} {place : Place}
    {info : PlaceInfo} {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (accepted : Core.validate module = .ok ())
    (environment : env = ⟨module, initImpl, initContext, []⟩)
    (source : tyPlace (initEnv module globalId) place start = .ok (info, finish))
    (replayed : rpPlace env place before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement (lowerGlobal module global).init after.eff target)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerGlobal module global).init target
      (lowerEnv env.mod env.impl.vars [global.ty]) scopeCount
      #[] ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerPlace place (lowerEnv env.mod env.impl.vars [global.ty]) ls).2)
    (placeChild : ∀ owner field, place = .field owner field →
      GlobalPlaceReplayAt (initEnv module globalId) env results vt (lowerGlobal module global).init [global.ty] #[] target scopeCount owner ls upper)
    (viewChild : ∀ view index origin, place = .elem view index origin →
      GlobalViewReplayAt (initEnv module globalId) env results vt (lowerGlobal module global).init [global.ty] #[] target scopeCount view ls upper)
    (expressionChild : ∀ expression state provenance,
      (place = .deref expression ∧ state = ls) ∨
        (∃ view origin, place = .elem view expression origin ∧
          state = (lowerView view (lowerEnv env.mod env.impl.vars [global.ty]) ls).2) →
      GlobalExpressionReplayAt (initEnv module globalId) env results vt (lowerGlobal module global).init [global.ty] #[] target scopeCount expression state provenance) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerGlobal module global).init target
        (lowerEnv env.mod env.impl.vars [global.ty]) scopeCount
        #[]
        (lowerPlace place (lowerEnv env.mod env.impl.vars [global.ty]) ls).2 next ∧
      ((lowerPlace place (lowerEnv env.mod env.impl.vars [global.ty]) ls).2.cur.isSome = true →
        (lowerPlace place (lowerEnv env.mod env.impl.vars [global.ty]) ls).1 <
          (lowerPlace place (lowerEnv env.mod env.impl.vars [global.ty]) ls).2.vals.size ∧
        RootsRefine (lowerGlobal module global).init
          (rootsAt next.vals (lowerPlace place (lowerEnv env.mod env.impl.vars [global.ty]) ls).1) sourceRoots) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
  subst env
  exact typedGlobalPlace (source_initializer_root_tables module globalId []) rfl source replayed wholeEffect ready generated native
    placeChild viewChild expressionChild

theorem typedInitializerView {env : PEnv} {module : Core.Module} {global : Core.Global} {globalId : GlobalId} {view : View} {info : Ty × Bool}
    {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (accepted : Core.validate module = .ok ())
    (environment : env = ⟨module, initImpl, initContext, []⟩)
    (source : tyView (initEnv module globalId) view start = .ok (info, finish))
    (replayed : rpView env view before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement (lowerGlobal module global).init after.eff target)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerGlobal module global).init target
      (lowerEnv env.mod env.impl.vars [global.ty]) scopeCount
      #[] ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerView view (lowerEnv env.mod env.impl.vars [global.ty]) ls).2)
    (placeChild : ∀ place, view = .of place → GlobalPlaceReplayAt (initEnv module globalId) env results vt (lowerGlobal module global).init [global.ty] #[] target scopeCount place ls upper)
    (expressionChild : ∀ expression, view = .val expression → GlobalExpressionReplayAt (initEnv module globalId) env results vt (lowerGlobal module global).init [global.ty] #[] target scopeCount expression ls upper) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerGlobal module global).init target
        (lowerEnv env.mod env.impl.vars [global.ty]) scopeCount
        #[]
        (lowerView view (lowerEnv env.mod env.impl.vars [global.ty]) ls).2 next ∧
      ((lowerView view (lowerEnv env.mod env.impl.vars [global.ty]) ls).2.cur.isSome = true →
        ReplayValue (lowerGlobal module global).init next
          (lowerView view (lowerEnv env.mod env.impl.vars [global.ty]) ls).2
          (lowerView view (lowerEnv env.mod env.impl.vars [global.ty]) ls).1 sourceRoots (.view .readOnly info.1)) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
  subst env
  exact typedGlobalView source replayed wholeEffect (global_initializer_parameterRoots_closed module global)
    ready generated native placeChild expressionChild

theorem typedInitializerRead {env : PEnv} {module : Core.Module} {global : Core.Global} {globalId : GlobalId} {place : Place} {type : Ty}
    {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (accepted : Core.validate module = .ok ())
    (environment : env = ⟨module, initImpl, initContext, []⟩)
    (source : tyExpr (initEnv module globalId) (.read place) start = .ok (type, finish))
    (replayed : rpExpr env (.read place) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement (lowerGlobal module global).init after.eff target)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerGlobal module global).init target
      (lowerEnv env.mod env.impl.vars [global.ty]) scopeCount #[] ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars [global.ty]) ls).2)
    (placeChild : GlobalPlaceReplayAt (initEnv module globalId) env results vt (lowerGlobal module global).init [global.ty] #[] target scopeCount place ls upper) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerGlobal module global).init target
        (lowerEnv env.mod env.impl.vars [global.ty]) scopeCount #[]
        (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars [global.ty]) ls).2 next ∧
      ((lowerExpr (.read place) (lowerEnv env.mod env.impl.vars [global.ty]) ls).2.cur.isSome = true →
        ReplayValue (lowerGlobal module global).init next (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars [global.ty]) ls).2
          (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars [global.ty]) ls).1 sourceRoots (.data type)) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
  subst env
  exact typedGlobalRead (source_initializer_readable module globalId accepted) rfl
    (source_initializer_root_tables module globalId []) (global_initializer_parameterRoots_closed module global)
    source replayed wholeEffect ready generated native placeChild

#print axioms typedInitializerPlace
#print axioms typedInitializerView
#print axioms typedInitializerRead

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
