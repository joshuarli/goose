import Goose.Lower.Validation.SummaryPreservationNativeCallOccurrences

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedCallNative {env : TEnv} {penv : PEnv} {calleeId : ContextId} {ctx : Context}
    {callee : Impl} {func : Func} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {target : Core.Eff} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
    {ls : LS} {upper : Prov} {syntaxArgs : List Arg} {origin : OriginId}
    {start finish : Nat} {type : Ty} {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder (lower penv.mod) results vt func target le scopeCount slots ls upper)
    (tables : SourceRootTables env penv)
    (accepted : Core.validate penv.mod = .ok ())
    (contextLookup : penv.mod.contexts[calleeId]? = some ctx)
    (implLookup : penv.mod.impls[ctx.impl]? = some callee)
    (closed : ParameterRootsClosed func)
    (bounded : RootsBelow results (moduleTypedResultUpper penv.mod))
    (source : tyExpr env (.call calleeId syntaxArgs origin) start = .ok (type, finish))
    (replayed : rpExpr penv (.call calleeId syntaxArgs origin) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (originBound : origin < le.mod.origins.size) (calleeBound : calleeId < le.sigs.size)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExpr (.call calleeId syntaxArgs origin) le ls).2)
    (argumentsChild : ∀ tn2 argumentRoots sourceAfter state provenance,
      tyArgs env callee callee.params.toList syntaxArgs start = .ok ((), tn2) →
      rpArgs penv syntaxArgs before = .ok (argumentRoots, sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder (lower penv.mod) results vt func target le scopeCount slots state provenance →
      state = ls → GeneratedBuilderState state →
      NativeRows vt (lowerArgs syntaxArgs le state).2 →
      ∃ next, ReplayBuilder (lower penv.mod) results vt func target le scopeCount slots
          (lowerArgs syntaxArgs le state).2 next ∧
        ((lowerArgs syntaxArgs le state).2.cur.isSome = true →
          (lowerArgs syntaxArgs le state).1.length = syntaxArgs.length ∧
          ∀ (index : Nat) (value : ValueId), (lowerArgs syntaxArgs le state).1[index]? = some value →
            value < (lowerArgs syntaxArgs le state).2.vals.size ∧
            ∃ roots, argumentRoots[index]? = some roots ∧ RootsRefine func (rootsAt next.vals value) roots) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder (lower penv.mod) results vt func target le scopeCount slots
        (lowerExpr (.call calleeId syntaxArgs origin) le ls).2 next ∧
      ((lowerExpr (.call calleeId syntaxArgs origin) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.call calleeId syntaxArgs origin) le ls).2
          (lowerExpr (.call calleeId syntaxArgs origin) le ls).1 sourceRoots (.data type)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, completed, value, retained, _⟩ := ready.typedCallNativeWithOrigins tables accepted contextLookup implLookup closed bounded source replayed wholeEffect originBound calleeBound generated native argumentsChild
  exact ⟨next, completed, value, retained⟩

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
