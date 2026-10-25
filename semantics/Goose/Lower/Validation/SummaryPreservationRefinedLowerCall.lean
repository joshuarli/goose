import Goose.Lower.Validation.SummaryPreservationRefinedEmitCall
import Goose.Lower.Validation.SummaryPreservationRefinedAppend
import Goose.Lower.Validation.SummaryPreservationLowerCall

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerExpr_call_refined_source_witness {env : PEnv} {calleeId : ContextId}
    {ctx : Context} {callee : Impl} {caller : Func} {upper : Prov}
    {vt : Array (Option VTy)} {results : Array (List RootRef)} {args : List ValueId}
    {syntaxArgs : List Arg} {sourceArgs : List (List RootRef)} {roots : List RootRef}
    {before after : RState} {origin : OriginId} {initial ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId}
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[calleeId]? = some ctx)
    (implLookup : env.mod.impls[ctx.impl]? = some callee)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt caller upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt caller upper before.eff ls)
    (closed : ParameterRootsClosed caller) (bounded : RootsBelow results (moduleRefinedResultUpper env.mod))
    (argumentCount : args.length = callee.params.size)
    (operandBounds : ∀ value ∈ args, value < ls.vals.size)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value →
      ∃ sourceRoots, sourceArgs[index]? = some sourceRoots ∧
        RootsRefine caller (rootsAt upper.vals value) sourceRoots)
    (argumentsRun : lowerArgs syntaxArgs le initial = (args, ls))
    (replay : rpCall env calleeId sourceArgs before = .ok (roots, after)) :
    ∃ next : Prov,
      BuilderRootWitness results vt caller next (lowerExpr (.call calleeId syntaxArgs origin) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt caller next after.eff
        (lowerExpr (.call calleeId syntaxArgs origin) le initial).2 ∧
      RootsRefine caller
        (rootsAt next.vals (lowerExpr (.call calleeId syntaxArgs origin) le initial).1) roots ∧
      next.slots = upper.slots := by
  obtain ⟨next, callWitness, callEffects, returned, slots⟩ := emitCall_refined_source_witness
    (origin := some origin) accepted contextLookup implLookup symbols current blockBound witness prior
    closed bounded argumentCount operandBounds arguments replay
  rw [lowerExpr_call_after_args argumentsRun]
  dsimp only
  split
  · have callCurrent : (emitDef (.call calleeId args (some origin)) le ls).2.cur = some block := by
      rw [emitDef_run _ _ current]
      exact current
    have callBlockBound : block < (emitDef (.call calleeId args (some origin)) le ls).2.blocks.size := by
      rw [emitDef_run _ _ current]
      simpa using blockBound
    have termWitness := emitTerm_refined_witness (le := le) (term := .unreachable) callCurrent callBlockBound
      callWitness callEffects True.intro (effectRefinement_empty caller after.eff)
    exact ⟨next, termWitness.1, termWitness.2, returned, slots⟩
  · exact ⟨next, callWitness, callEffects, returned, slots⟩

end Goose.Lower.Validation.SummaryPreservation
