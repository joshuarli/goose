import Goose.Lower.Validation.SummaryPreservationAssignOpLoad
import Goose.Lower.Validation.SummaryPreservationRefinedAppend

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerStmt_assignOp_after_rhs {op : BinOp} {place : Place} {expression : Expr}
    {org : OriginId} {initial placeLS loadedLS ls : LS} {le : LEnv}
    {address old rhs : ValueId} {ty : IntTy} (loop : Option LoopCtx)
    (placeRun : lowerPlace place le initial = (address, placeLS))
    (loadRun : emitDef (.load address) le placeLS = (old, loadedLS))
    (valueRun : lowerExpr expression le loadedLS = (rhs, ls))
    (typeRun : intTyOf old le ls = (ty, ls)) :
    lowerStmt loop (.assignOp op place expression org) le initial =
      (do let result ← emitDef (.bin op ty old rhs (some org))
          emitEffect (.store address result (some org))) le ls := by
  simp only [lowerStmt, bind_run, placeRun, loadRun, valueRun, typeRun]

theorem lowerStmt_assignOp_source_witness {env : PEnv} {context : ContextId}
    {op : BinOp} {place : Place} {expression : Expr} {org : OriginId}
    {initialSource placeState before after : RState} {placeRoots valueRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {initial placeLS loadedLS ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId}
    {address old rhs : ValueId} {ty : IntTy} {target : Core.Eff} (loop : Option LoopCtx)
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[context]? = some env.ctx)
    (implLookup : env.mod.impls[env.ctx.impl]? = some env.impl)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before))
    (source : rpStmt env (.assignOp op place expression org) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (placeRun : lowerPlace place le initial = (address, placeLS))
    (loadRun : emitDef (.load address) le placeLS = (old, loadedLS))
    (valueRun : lowerExpr expression le loadedLS = (rhs, ls))
    (typeRun : intTyOf old le ls = (ty, ls))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper target ls)
    (roots : RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsAt upper.vals address) placeRoots)
    (owner : (ownerTy vt address).any Ty.isRefLike = false)
    (addressBound : address < ls.vals.size) (oldBound : old < ls.vals.size)
    (rhsBound : rhs < ls.vals.size) (originBound : org < le.mod.origins.size) :
    ∃ next : Prov,
      BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) next
        (lowerStmt loop (.assignOp op place expression org) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (lowerContextAt env.mod env.ctx env.impl) next target
        (lowerStmt loop (.assignOp op place expression org) le initial).2 ∧
      next.slots = upper.slots ∧
      (lowerStmt loop (.assignOp op place expression org) le initial).2.SymbolWF le scopeCount ∧
      (lowerStmt loop (.assignOp op place expression org) le initial).2.cur = some block ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have deltas := assignOp_instruction_effects (vt := vt) (loadRoots := upper) (storeRoots := upper)
    (old := old) (rhs := rhs) (result := ls.vals.size) (ty := ty)
    accepted contextLookup implLookup placeReplay valueReplay source roots roots owner wholeEffect
  obtain ⟨next, nextRoots, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, valueBound, growth⟩ := emitDef_refined_frame_growth
      (.bin op ty old rhs (some org)) symbols current blockBound witness prior
      (by simpa [Op.uses] using And.intro oldBound rhsBound)
      (by simpa [Op.origin] using originBound)
      (by simp [Op.SymbolRefsValid]) deltas.2.1
  let emitted := emitDef (.bin op ty old rhs (some org)) le ls
  have emptyValue : rootsAt next.vals emitted.1 = [] := by
    rw [returned]
    rfl
  have addressUpper : address < upper.vals.size := by simpa [witness.valueSize] using addressBound
  have nextAddress : RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsAt next.vals address) placeRoots := by rw [growth address addressUpper]; exact roots
  have storeDelta := (assignOp_instruction_effects (vt := vt) (loadRoots := next)
    (storeRoots := next) (old := old) (rhs := rhs) (result := emitted.1) (ty := ty)
    accepted contextLookup implLookup placeReplay valueReplay source nextAddress nextAddress owner
    wholeEffect).2.2
  have storeClosed : InstructionRootsClosed results vt
      { lowerContextAt env.mod env.ctx env.impl with blocks := finishBlocks emitted.2.blocks } next
      (.eff (.store address emitted.1 (some org))) := by
    intro slot slotMember root member
    rw [emptyValue] at member
    cases member
  have completed := emitEffect_refined_witness (le := le) nextCurrent nextBlockBound nextRoots effects storeClosed storeDelta
  have addressFinal : address < emitted.2.vals.size := by
    dsimp only [emitted]
    rw [emitDef_run _ _ current]
    simpa using Nat.lt_succ_of_lt addressBound
  have completedSymbols : (emitEffect (.store address emitted.1 (some org)) le emitted.2).2.SymbolWF le scopeCount := by
    rw [emitEffect_run _ _ nextCurrent]
    apply LS.SymbolWF.emitEffect nextSymbols nextBlockBound
    apply Inst.SymbolsWithin.eff
    · simpa [Effect.uses] using And.intro addressFinal valueBound
    · simpa [Effect.origin] using originBound
    · simp [Effect.SymbolRefsValid]
  rw [lowerStmt_assignOp_after_rhs loop placeRun loadRun valueRun typeRun]
  simp only [bind_run]
  refine ⟨next, completed.1, completed.2, slots, completedSymbols, ?_, growth⟩
  rw [emitEffect_run _ _ nextCurrent]
  exact nextCurrent

end Goose.Lower.Validation.SummaryPreservation
