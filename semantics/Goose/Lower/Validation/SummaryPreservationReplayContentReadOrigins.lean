import Goose.Lower.Validation.SummaryPreservationReplayContentReadNestedOrigins

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem contentReadWithOrigins {env : PEnv} {context : ContextId} {index : Nat} {param : Param} {localVar : LocalVar}
    {before after : RState} {sourceRoots : List RootRef} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {siteRoot : DemandNode} {scopeCount : Nat} {ls : LS} {upper : Prov}
    {mutability : Mutability} {element : Ty}
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (parameter : env.impl.params[index]? = some param)
    (variableRow : env.impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (source : rpExpr env (.read (.deref (.read (.var param.var)))) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (addressType : ls.cur.isSome = true → vt[(lowerExpr (.read (.var param.var))
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1]? = some (some (.data localVar.ty)))
    (sliceType : ls.cur.isSome = true → vt[(lowerExpr (.read (.var param.var))
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size]? =
        some (some (.data (.slice mutability element))))
    (metadata : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot
      (lowerContextAt env.mod env.ctx env.impl)
      (lowerExpr (.read (.deref (.read (.var param.var))))
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerExpr (.read (.deref (.read (.var param.var))))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      ((lowerExpr (.read (.deref (.read (.var param.var))))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerExpr (.read (.deref (.read (.var param.var))))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
          (lowerExpr (.read (.deref (.read (.var param.var))))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1
          sourceRoots (.data (.slice mutability element))) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ((lowerExpr (.read (.deref (.read (.var param.var))))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ∃ placeRoots placeAfter, rpPlace env (.deref (.read (.var param.var))) before = .ok (placeRoots, placeAfter) ∧
          (lowerPlace (.deref (.read (.var param.var))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 <
            (lowerExpr (.read (.deref (.read (.var param.var))))
              (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size ∧
          RootsRefine (lowerContextAt env.mod env.ctx env.impl)
            (rootsAt next.vals (lowerPlace (.deref (.read (.var param.var)))
              (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1) placeRoots) := by
  obtain ⟨next, completed, value, retained, origins, _, _⟩ := ready.contentReadWithNestedOrigins
    accepted contextRow implementationRow parameter variableRow reference source wholeEffect addressType sliceType metadata
  exact ⟨next, completed, value, retained, origins⟩

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
