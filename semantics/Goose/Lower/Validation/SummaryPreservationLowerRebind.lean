import Goose.Lower.Validation.SummaryPreservationRebindSource
import Goose.Lower.Validation.SummaryPreservationRefinedAppend

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerStmt_rebind_source_witness {env : PEnv} {context : ContextId} {varId : VarId}
    {expression : Expr} {org : OriginId} {localVar : LocalVar} {sourceRoots : List RootRef}
    {initialSource before after : RState} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {upper : Prov} {initial ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId}
    {value : ValueId} (loop : Option LoopCtx)
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[context]? = some env.ctx)
    (implLookup : env.mod.impls[env.ctx.impl]? = some env.impl)
    (variableRow : env.impl.vars[varId]? = some localVar)
    (reference : localVar.ty.isRefLike = true) (ordinary : localVar.ty.isRefSlice = false)
    (operandSource : rpExpr env expression initialSource = .ok (sourceRoots, before))
    (source : rpStmt env (.rebind varId expression org) initialSource = .ok ((), after))
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
        (lowerStmt loop (.rebind varId expression org) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (lowerContextAt env.mod env.ctx env.impl) next after.eff
        (lowerStmt loop (.rebind varId expression org) le initial).2 ∧
      next.slots = upper.slots ∧
      (lowerStmt loop (.rebind varId expression org) le initial).2.SymbolWF le scopeCount ∧
      (lowerStmt loop (.rebind varId expression org) le initial).2.cur = some block := by
  let func := lowerContextAt env.mod env.ctx env.impl
  have contract := rpStmt_rebind_contract operandSource source
  have priorAfter : BuilderEffectRefinement (lower env.mod) vt func upper after.eff ls := by
    intro inst member
    rw [contract.2]
    split
    · have old := prior inst member
      exact ⟨old.reads, old.writes, old.grows, old.shrinks,
        fun target h => addTargets_left _ _ target (old.rebinds target h),
        old.aborts, old.outputs, old.unknown⟩
    · exact prior inst member
  let coerced := coerceSlot varId value org le ls
  obtain ⟨middle, middleWitness, middleEffects, middleRoots, middleSlots, middleSymbols,
    middleCurrent, middleBlockBound, middleValueBound⟩ :=
    coerceSlot_refined_witness varId org symbols current blockBound witness priorAfter valueBound roots originBound
  let address := emitDef (.slotAddr varId) le coerced.2
  obtain ⟨next, nextWitness, nextEffects, addressRoots, nextSlots, growth⟩ :=
    emitDef_refined_witness_growth middleSymbols middleCurrent middleBlockBound middleWitness middleEffects
      (op := .slotAddr varId) (value := address.1) (final := address.2)
      (by simp [Op.uses]) (effectRefinement_empty func after.eff) rfl
  have nextValueRoots : RootsRefine func (rootsAt next.vals coerced.1) sourceRoots := by
    rw [growth coerced.1 (by rw [middleWitness.valueSize]; exact middleValueBound)]
    exact middleRoots
  have nextSlotRoots : next.slots = typedContextSlotUpper env.mod env.ctx env.impl :=
    nextSlots.trans (middleSlots.trans slots)
  have addressCurrent : address.2.cur = some block := by
    dsimp [address]
    rw [emitDef_run _ _ middleCurrent]
    exact middleCurrent
  have addressBlockBound : block < address.2.blocks.size := by
    dsimp [address]
    rw [emitDef_run _ _ middleCurrent]
    simpa using middleBlockBound
  have addressSymbols : address.2.SymbolWF le scopeCount :=
    lowerPlace_var_symbols middleSymbols middleCurrent middleBlockBound varId slotBound
  obtain ⟨checkedImpl, lookup, contextOk⟩ := (validate_modOk env.mod accepted).ctx context env.ctx contextLookup
  rw [implLookup] at lookup
  cases lookup
  have stored : InstructionRootsClosed results vt
      { func with blocks := finishBlocks address.2.blocks } next
      (.eff (.store address.1 coerced.1 (some org))) := by
    intro slot slotMember root rootMember
    rw [addressRoots] at slotMember
    have same : slot = varId := RootRef.local.inj (List.mem_singleton.mp slotMember)
    subst slot
    rw [nextSlotRoots]
    exact bindRootsV_typed_slot_bound contextOk.annotationShape variableRow ordinary contract.1
      nextValueRoots root rootMember
  have delta := effectStep_rebind_refines_from_source (vt := vt) (value := coerced.1)
    variableRow reference addressRoots operandSource source
  have storedWitness := emitEffect_refined_witness (le := le) addressCurrent addressBlockBound
    nextWitness nextEffects stored delta
  have addressBound : address.1 < address.2.vals.size := by
    dsimp [address]
    rw [emitDef_run _ _ middleCurrent]
    simp
  have valueAfterAddress : coerced.1 < address.2.vals.size := by
    dsimp [address]
    rw [emitDef_run _ _ middleCurrent]
    simp only [Array.size_push]
    exact Nat.lt_succ_of_lt middleValueBound
  have storeSymbols : (emitEffect (.store address.1 coerced.1 (some org)) le address.2).2.SymbolWF le scopeCount := by
    rw [emitEffect_run _ _ addressCurrent]
    apply LS.SymbolWF.emitEffect addressSymbols addressBlockBound
    apply Inst.SymbolsWithin.eff
    · simpa [Effect.uses] using And.intro addressBound valueAfterAddress
    · simpa [Effect.origin] using originBound
    · simp [Effect.SymbolRefsValid]
  have whole : lowerStmt loop (.rebind varId expression org) le initial =
      emitEffect (.store address.1 coerced.1 (some org)) le address.2 := by
    simp only [lowerStmt, bind_run, operandRun]
    rfl
  rw [whole]
  refine ⟨next, storedWitness.1, storedWitness.2, nextSlots.trans middleSlots, storeSymbols, ?_⟩
  rw [emitEffect_run _ _ addressCurrent]
  exact addressCurrent

end Goose.Lower.Validation.SummaryPreservation
