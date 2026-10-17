import Goose.Lower.Validation.SummaryPreservationReplayLiveEmit
import Goose.Lower.Validation.SummaryPreservationReplayTerm
import Goose.Lower.Validation.SummaryPreservationTypedCallRoots
import Goose.Lower.Validation.SummaryPreservationRefinedCalls
import Goose.Lower.Validation.SummaryPreservationRefinedCallEffects
import Goose.Lower.Validation.SummaryPreservationLowerCall

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem callEmitted {env : PEnv} {calleeId : ContextId} {ctx : Context} {callee : Impl}
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
      (ls.cur.isSome = true →
        ReplayValue func next (lowerExpr (.call calleeId syntaxArgs origin) le initial).2
          (lowerExpr (.call calleeId syntaxArgs origin) le initial).1 sourceRoots
          (.data ((callee.results[0]?).getD Ty.unit))) := by
  obtain ⟨next, generated, returned, retained⟩ := ready.emitTypedDef_live
    (.call calleeId args (some origin)) sourceRoots (.data ((callee.results[0]?).getD Ty.unit))
    (fun live => by simpa [Op.uses] using operandBounds live)
    (fun candidate row => by cases row; exact originBound)
    calleeBound
    (fun live => (effectStep_call_refines_from_source accepted contextLookup implLookup closed
      (arguments live) replayed).trans effectBound)
    (fun live => rootsOfDef_call_refines_from_source accepted contextLookup implLookup
      (fun index root member => typedResultUpper_below_refined env.mod index root
        (bounded index root member)) (argumentCount live) (arguments live) replayed)
    (fun _ nonref => rootsOfDef_call_default_nonref_empty bounded contextLookup implLookup
      nonref vt func upper ls.vals.size args (some origin))
  have emittedLive (live : ls.cur.isSome = true) :
      (Goose.Lower.emitDef (.call calleeId args (some origin)) le ls).2.cur.isSome = true := by
    cases current : ls.cur with
    | none => simp [current] at live
    | some block => rw [emitDef_run _ _ current]; simp [current]
  rw [lowerExpr_call_after_args argumentsRun]
  dsimp only
  split
  · refine ⟨next, generated.unreachable, ?_, retained, ?_⟩
    · intro live
      cases current : (Goose.Lower.emitDef (.call calleeId args (some origin)) le ls).2.cur with
      | none => rw [emitTerm_none _ _ current] at live; simp [current] at live
      | some block => rw [emitTerm_run _ _ current] at live; simp at live
    · intro live
      have value := returned (emittedLive live)
      refine ⟨?_, value.refined, value.scalar⟩
      cases current : (Goose.Lower.emitDef (.call calleeId args (some origin)) le ls).2.cur with
      | none => rw [emitTerm_none _ _ current]; exact value.bound
      | some block => rw [emitTerm_run _ _ current]; exact value.bound
  · exact ⟨next, generated, returned, retained, fun live => returned (emittedLive live)⟩

#print axioms callEmitted

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
