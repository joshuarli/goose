import Goose.Lower.Validation.SummaryPreservationLetSource
import Goose.Lower.Validation.SummaryPreservationRefinedAppend

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerStmt_reference_let_source_witness {env : PEnv} {context : ContextId} {varId : VarId}
    {expression : Expr} {org : OriginId} {localVar : LocalVar} {sourceRoots : List RootRef}
    {initialSource before after : RState} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {upper : Prov} {initial ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId}
    {value : ValueId} (loop : Option LoopCtx)
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[context]? = some env.ctx)
    (implLookup : env.mod.impls[env.ctx.impl]? = some env.impl)
    (variableRow : env.impl.vars[varId]? = some localVar)
    (reference : localVar.ty.isRefLike = true) (ordinary : localVar.ty.isRefSlice = false)
    (operandSource : rpExpr env expression { initialSource with nextVar := initialSource.nextVar + 1 } =
      .ok (sourceRoots, before))
    (source : rpStmt env (.letS varId expression org) initialSource = .ok ((), after))
    (operandRun : lowerExpr expression le initial = (value, ls))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper before.eff ls)
    (valueBound : value < ls.vals.size)
    (roots : RootsRefine (lowerContextAt env.mod env.ctx env.impl) (rootsAt upper.vals value) sourceRoots)
    (slots : upper.slots = typedContextSlotUpper env.mod env.ctx env.impl)
    (slotBound : varId < le.slots.size) (originBound : org < le.mod.origins.size) :
    ∃ next : Prov,
      BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) next
        (lowerStmt loop (.letS varId expression org) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (lowerContextAt env.mod env.ctx env.impl) next after.eff
        (lowerStmt loop (.letS varId expression org) le initial).2 ∧
      next.slots = upper.slots ∧
      (lowerStmt loop (.letS varId expression org) le initial).2.SymbolWF le scopeCount ∧
      (lowerStmt loop (.letS varId expression org) le initial).2.cur = some block := by
  obtain ⟨binding, same⟩ := rpStmt_reference_let_contract variableRow reference operandSource source
  subst after
  let func := lowerContextAt env.mod env.ctx env.impl
  let coerced := coerceSlot varId value org le ls
  obtain ⟨next, nextWitness, nextEffects, nextRoots, nextSlots, nextSymbols,
    nextCurrent, nextBlockBound, nextValueBound⟩ :=
    coerceSlot_refined_witness varId org symbols current blockBound witness prior valueBound roots originBound
  obtain ⟨checkedImpl, lookup, contextOk⟩ := (validate_modOk env.mod accepted).ctx context env.ctx contextLookup
  rw [implLookup] at lookup
  cases lookup
  have stored : InstructionRootsClosed results vt
      { func with blocks := finishBlocks coerced.2.blocks } next
      (.eff (.slotInit varId coerced.1 (some org))) := by
    intro root member
    rw [nextSlots, slots]
    exact bindRootsV_typed_slot_bound contextOk.annotationShape variableRow ordinary binding nextRoots root member
  have completed := emitEffect_refined_witness (le := le) nextCurrent nextBlockBound
    nextWitness nextEffects stored (effectRefinement_empty func before.eff)
  have completedSymbols : (emitEffect (.slotInit varId coerced.1 (some org)) le coerced.2).2.SymbolWF
      le scopeCount := by
    rw [emitEffect_run _ _ nextCurrent]
    apply LS.SymbolWF.emitEffect nextSymbols nextBlockBound
    apply Inst.SymbolsWithin.eff
    · simpa [Effect.uses] using nextValueBound
    · simpa [Effect.origin] using originBound
    · simpa [Effect.SymbolRefsValid] using slotBound
  have whole : lowerStmt loop (.letS varId expression org) le initial =
      emitEffect (.slotInit varId coerced.1 (some org)) le coerced.2 := by
    simp only [lowerStmt, bind_run, operandRun]
    rfl
  rw [whole]
  refine ⟨next, completed.1, completed.2, nextSlots, completedSymbols, ?_⟩
  rw [emitEffect_run _ _ nextCurrent]
  exact nextCurrent

end Goose.Lower.Validation.SummaryPreservation
