import Goose.Lower.Validation.SummaryPreservationRefinedEmitCall
import Goose.Lower.Validation.SummaryPreservationTypedResultBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitCall_nonref_source_witness {env : PEnv} {calleeId : ContextId}
    {ctx : Context} {callee : Impl} {caller : Func} {upper : Prov} {resultType : Ty}
    {vt : Array (Option VTy)} {results : Array (List RootRef)} {args : List ValueId}
    {sourceArgs : List (List RootRef)} {roots : List RootRef} {before after : RState}
    {origin : Option OriginId} {ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId}
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[calleeId]? = some ctx)
    (implLookup : env.mod.impls[ctx.impl]? = some callee)
    (resultLookup : callee.results[0]? = some resultType)
    (nonReference : resultType.isRefLike = false)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt caller upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt caller upper before.eff ls)
    (closed : ParameterRootsClosed caller)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (operandBounds : ∀ value ∈ args, value < ls.vals.size)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value →
      ∃ sourceRoots, sourceArgs[index]? = some sourceRoots ∧
        RootsRefine caller (rootsAt upper.vals value) sourceRoots)
    (replay : rpCall env calleeId sourceArgs before = .ok (roots, after)) :
    ∃ next : Prov,
      BuilderRootWitness results vt caller next (emitDef (.call calleeId args origin) le ls).2 ∧
      BuilderEffectRefinement (lower env.mod) vt caller next after.eff
        (emitDef (.call calleeId args origin) le ls).2 ∧
      rootsAt next.vals (emitDef (.call calleeId args origin) le ls).1 = [] ∧
      next.slots = upper.slots := by
  have priorAfter : BuilderEffectRefinement (lower env.mod) vt caller upper after.eff ls := by
    intro inst member
    exact (prior inst member).source_mono
      (PMono.rpCall env calleeId sourceArgs before roots after replay).2
      (PMonoRebinds.rpCall env calleeId sourceArgs before roots after replay)
      (PFlagsMono.rpCall env calleeId sourceArgs before roots after replay)
  have delta := effectStep_call_refines_from_source (vt := vt) (result := ls.vals.size) (origin := origin)
    accepted contextLookup implLookup closed arguments replay
  obtain ⟨next, nextWitness, nextEffects, returned, slots⟩ := emitDef_refined_witness
    symbols current blockBound witness priorAfter (op := .call calleeId args origin)
    (value := (emitDef (.call calleeId args origin) le ls).1)
    (final := (emitDef (.call calleeId args origin) le ls).2)
    operandBounds delta rfl
  refine ⟨next, nextWitness, nextEffects, ?_, slots⟩
  rw [returned]
  exact rootsOfDef_call_nonref_empty bounded contextLookup implLookup resultLookup nonReference _ _ _ _ _ _

end Goose.Lower.Validation.SummaryPreservation
