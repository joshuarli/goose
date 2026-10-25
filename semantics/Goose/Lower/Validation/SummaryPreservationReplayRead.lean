import Goose.Lower.Validation.SummaryPreservationReplayReadOrigins

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem readExpression {typingEnv : TEnv} {env : PEnv} {context : ContextId} {place : Place} {ty : Ty}
    {typingStart typingFinish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {siteRoot : DemandNode}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (checked : SourceReadableEnvironment typingEnv) (tables : SourceRootTables typingEnv env)
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (typed : tyExpr typingEnv (.read place) typingStart = .ok (ty, typingFinish))
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (source : rpExpr env (.read place) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (placeStep : ∀ (info : PlaceInfo) (finish : Nat),
      tyPlace typingEnv place typingStart = .ok (info, finish) →
      ∀ roots state, rpPlace env place before = .ok (roots, state) →
      ∃ middle, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
          (typedContextSlotUpper env.mod env.ctx env.impl)
          (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 middle ∧
        ((lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
          (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 <
            (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size ∧
          RootsRefine (lowerContextAt env.mod env.ctx env.impl)
            (rootsAt middle.vals (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1) roots) ∧
        ∀ old, old < upper.vals.size → rootsAt middle.vals old = rootsAt upper.vals old)
    (resultType : (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
      vt[(lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size]? =
        some (some (.data ty)))
    (holderType : ∀ (variableId : VarId) (localVar : LocalVar),
      place = .deref (.read (.var variableId)) → typingEnv.vars[variableId]? = some localVar →
      localVar.ty.isRefSlice = true → ls.cur.isSome = true →
      vt[(lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1]? =
        some (some (.data localVar.ty)))
    (metadata : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot
      (lowerContextAt env.mod env.ctx env.impl)
      (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      ((lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
          (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 sourceRoots (.data ty)) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
  obtain ⟨next, completed, value, retained, _⟩ := readExpressionWithOrigins checked tables contextRow implementationRow typed ready source wholeEffect placeStep resultType holderType metadata
  exact ⟨next, completed, value, retained⟩

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
