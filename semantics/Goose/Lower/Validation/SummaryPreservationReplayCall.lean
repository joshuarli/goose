import Goose.Lower.Validation.SummaryPreservationReplayCallEmitted

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem call {env : PEnv} {calleeId : ContextId} {ctx : Context} {callee : Impl}
    {func : Func} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {target : Core.Eff} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
    {initial ls : LS} {upper : Prov} {args : List ValueId} {syntaxArgs : List Arg}
    {sourceArgs : List (List RootRef)} {sourceRoots : List RootRef}
    {before after : RState} {origin : OriginId}
    (ready : ReplayBuilder (lower env.mod) results vt func target le scopeCount slots ls upper)
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[calleeId]? = some ctx)
    (implLookup : env.mod.impls[ctx.impl]? = some callee)
    (closed : ParameterRootsClosed func)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (argumentCount : ls.cur.isSome = true → args.length = callee.params.size)
    (operandBounds : ls.cur.isSome = true → ∀ value ∈ args, value < ls.vals.size)
    (arguments : ls.cur.isSome = true → ∀ (index : Nat) (value : ValueId),
      args[index]? = some value → ∃ sourceRoots, sourceArgs[index]? = some sourceRoots ∧
        RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : origin < le.mod.origins.size)
    (calleeBound : calleeId < le.sigs.size)
    (argumentsRun : lowerArgs syntaxArgs le initial = (args, ls))
    (replayed : rpCall env calleeId sourceArgs before = .ok (sourceRoots, after))
    (effectBound : EffectRefinement func after.eff target) :
    ∃ next, ReplayBuilder (lower env.mod) results vt func target le scopeCount slots
        (lowerExpr (.call calleeId syntaxArgs origin) le initial).2 next ∧
      ((lowerExpr (.call calleeId syntaxArgs origin) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.call calleeId syntaxArgs origin) le initial).2
          (lowerExpr (.call calleeId syntaxArgs origin) le initial).1 sourceRoots
          (.data ((callee.results[0]?).getD Ty.unit))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, completed, value, retained, _⟩ := ready.callEmitted accepted contextLookup implLookup
    closed bounded argumentCount operandBounds arguments originBound calleeBound argumentsRun replayed effectBound
  exact ⟨next, completed, value, retained⟩

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
