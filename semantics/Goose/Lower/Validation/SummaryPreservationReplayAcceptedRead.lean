import Goose.Lower.Validation.SummaryPreservationReplayAcceptedReadOrigins

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem acceptedLocalRead {env : PEnv} {context : ContextId} {variableId : VarId} {localVar : LocalVar}
    {before after : RState} {sourceRoots : List RootRef} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {ls : LS} {upper : Prov}
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (variableRow : env.impl.vars[variableId]? = some localVar)
    (source : rpExpr env (.read (.var variableId)) before = .ok (sourceRoots, after))
    (scalarType : ls.cur.isSome = true → localVar.ty.isRefLike = false →
      valRefLike vt (ls.vals.size + 1) = false) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      ((lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
          (lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1
          sourceRoots (.data localVar.ty) ∧
        rootsAt next.vals (lowerExpr (.read (.var variableId))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 =
          if valRefLike vt (lowerExpr (.read (.var variableId))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 then
            rootsAt (typedContextSlotUpper env.mod env.ctx env.impl) variableId else []) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, completed, value, retained, _⟩ := ready.acceptedLocalReadWithOrigins
    accepted contextRow implementationRow variableRow source scalarType
  exact ⟨next, completed, value, retained⟩

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
