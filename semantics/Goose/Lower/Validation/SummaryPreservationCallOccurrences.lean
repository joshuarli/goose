import Goose.Lower.Validation.SummaryPreservationReplayCall
import Goose.Lower.Validation.SummaryPreservationArgumentAnnotations

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem callWithArgumentOrigins {env : PEnv} {calleeId : ContextId} {ctx : Context} {callee : Impl}
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
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      (ls.cur.isSome = true → ∀ (index : Nat) (value : ValueId), args[index]? = some value →
        (∃ roots, sourceArgs[index]? = some roots ∧ RootsRefine func (rootsAt next.vals value) roots) ∧
        (RootRef.param index ∈ (lowerContextAt env.mod ctx callee).parameterRoots index ∨
          ∀ root ∈ mapArgumentRoots func next value index,
            root ∈ (lowerContextAt env.mod ctx callee).parameterRoots index)) ∧
      (ls.cur.isSome = true →
        ReplayValue func next (lowerExpr (.call calleeId syntaxArgs origin) le initial).2
          (lowerExpr (.call calleeId syntaxArgs origin) le initial).1 sourceRoots
          (.data ((callee.results[0]?).getD Ty.unit))) := by
  obtain ⟨next, completed, returned, retained, emitted⟩ := ready.callEmitted accepted contextLookup implLookup
    closed bounded argumentCount operandBounds arguments originBound calleeBound argumentsRun replayed effectBound
  refine ⟨next, completed, returned, retained, ?_, emitted⟩
  intro live index value valueRow
  have indexBound := (List.getElem?_eq_some_iff.mp valueRow).1
  have parameterBound : index < callee.params.size := by rw [argumentCount live] at indexBound; exact indexBound
  obtain ⟨roots, sourceRow, refined⟩ := arguments live index value valueRow
  have valueBound := operandBounds live value (List.mem_of_getElem? valueRow)
  have retainedRoots := retained value (by simpa only [ready.roots.valueSize] using valueBound)
  constructor
  · refine ⟨roots, sourceRow, ?_⟩
    rw [retainedRoots]
    exact refined
  · apply accepted_call_argument_domain accepted contextLookup implLookup rfl parameterBound replayed
    rw [retainedRoots, sourceRow]
    exact refined

#print axioms callWithArgumentOrigins

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
