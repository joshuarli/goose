import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsCommon
import Goose.Lower.Validation.SummaryPreservationLowerAssignOp

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem occurrenceAssignOp_instruction_effects {env : PEnv} {func : Func}
    {op : BinOp} {place : Place} {expression : Expr} {org : OriginId}
    {initial placeState before after : RState} {placeRoots valueRoots : List RootRef}
    {vt : Array (Option VTy)} {loadRoots storeRoots : Prov}
    {address old rhs result : ValueId} {ty : IntTy} {target : Core.Eff}
    (closed : ParameterRootsClosed func)
    (placeReplay : rpPlace env place initial = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before))
    (source : rpStmt env (.assignOp op place expression org) initial = .ok ((), after))
    (loadRefines : GIR.RootsRefine (func)
      (rootsAt loadRoots.vals address) placeRoots)
    (storeRefines : GIR.RootsRefine (func)
      (rootsAt storeRoots.vals address) placeRoots)
    (owner : (ownerTy vt address).any Ty.isRefLike = false)
    (wholeEffect : EffectRefinement (func) after.eff target) :
    EffectRefinement (func)
        ((func).effectStep (lower env.mod) vt loadRoots {}
          (.def old (.load address))) target ∧
      EffectRefinement (func)
        ((func).effectStep (lower env.mod) vt storeRoots {}
          (.def result (.bin op ty old rhs (some org)))) target ∧
      EffectRefinement (func)
        ((func).effectStep (lower env.mod) vt storeRoots {}
          (.eff (.store address result (some org)))) target := by
  rw [rpStmt_assignOp_after_operands placeReplay valueReplay] at source
  cases source
  have loadBound := effectStep_load_refines (module := lower env.mod) (vt := vt)
    (provenance := loadRoots) (result := old) closed
    (effectRefinement_empty (func) before.eff) loadRefines
  have binBound := effectStep_bin_refines (module := lower env.mod) (vt := vt)
    (provenance := storeRoots) (result := result) (left := old) (right := rhs)
    (op := op) (ty := ty) (origin := some org)
    (effectRefinement_empty (func) before.eff)
  have storeBound := effectStep_store_nonref_refines_closed (module := lower env.mod) (vt := vt) (provenance := storeRoots)
    (value := result) (origin := org) (source := before.eff)
    closed storeRefines owner
  exact ⟨(loadBound.trans effectRefinement_assignOp_reads).trans wholeEffect,
    (binBound.trans effectRefinement_assignOp_bin).trans wholeEffect,
    (storeBound.trans effectRefinement_assignOp_writes).trans wholeEffect⟩


private theorem global_lowerStmt_assignOp_source_witness {env : PEnv} {func : Func}
    {op : BinOp} {place : Place} {expression : Expr} {org : OriginId}
    {initialSource placeState before after : RState} {placeRoots valueRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {initial placeLS loadedLS ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId}
    {address old rhs : ValueId} {ty : IntTy} {target : Core.Eff} (loop : Option LoopCtx)
    (closed : ParameterRootsClosed func)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before))
    (source : rpStmt env (.assignOp op place expression org) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement (func) after.eff target)
    (placeRun : lowerPlace place le initial = (address, placeLS))
    (loadRun : emitDef (.load address) le placeLS = (old, loadedLS))
    (valueRun : lowerExpr expression le loadedLS = (rhs, ls))
    (typeRun : intTyOf old le ls = (ty, ls))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness results vt (func) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (func) upper target ls)
    (roots : GIR.RootsRefine (func)
      (rootsAt upper.vals address) placeRoots)
    (owner : (ownerTy vt address).any Ty.isRefLike = false)
    (addressBound : address < ls.vals.size) (oldBound : old < ls.vals.size)
    (rhsBound : rhs < ls.vals.size) (originBound : org < le.mod.origins.size) :
    ∃ next : Prov,
      BuilderRootWitness results vt (func) next
        (lowerStmt loop (.assignOp op place expression org) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (func) next target
        (lowerStmt loop (.assignOp op place expression org) le initial).2 ∧
      next.slots = upper.slots ∧
      (lowerStmt loop (.assignOp op place expression org) le initial).2.SymbolWF le scopeCount ∧
      (lowerStmt loop (.assignOp op place expression org) le initial).2.cur = some block ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have deltas := occurrenceAssignOp_instruction_effects (vt := vt) (loadRoots := upper) (storeRoots := upper)
    (old := old) (rhs := rhs) (result := ls.vals.size) (ty := ty)
    closed placeReplay valueReplay source roots roots owner wholeEffect
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
  have nextAddress : GIR.RootsRefine (func)
      (rootsAt next.vals address) placeRoots := by rw [growth address addressUpper]; exact roots
  have storeDelta := (occurrenceAssignOp_instruction_effects (vt := vt) (loadRoots := next)
    (storeRoots := next) (old := old) (rhs := rhs) (result := emitted.1) (ty := ty)
    closed placeReplay valueReplay source nextAddress nextAddress owner
    wholeEffect).2.2
  have storeClosed : InstructionRootsClosed results vt
      { func with blocks := finishBlocks emitted.2.blocks } next
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


namespace ReplayBuilder

theorem occurrenceAssignOpAfterRhs {env : PEnv} {func : Func}
    {op : BinOp} {place : Place} {expression : Expr} {origin : OriginId}
    {initialSource placeState before after : RState} {placeRoots valueRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {initial placeLS loadedLS ls : LS} {le : LEnv} {scopeCount : Nat}
    {address old rhs : ValueId} {ty : IntTy} {target : Core.Eff}
    {slots : Array (List RootRef)} (loop : Option LoopCtx)
    (closed : ParameterRootsClosed func)
    (ready : ReplayBuilder (lower env.mod) results vt (func)
      target le scopeCount slots ls upper)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before))
    (source : rpStmt env (.assignOp op place expression origin) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement (func) after.eff target)
    (placeRun : lowerPlace place le initial = (address, placeLS))
    (loadRun : Goose.Lower.emitDef (.load address) le placeLS = (old, loadedLS))
    (valueRun : lowerExpr expression le loadedLS = (rhs, ls))
    (typeRun : intTyOf old le ls = (ty, ls))
    (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧ old < ls.vals.size ∧ rhs < ls.vals.size ∧
      GIR.RootsRefine (func) (rootsAt upper.vals address) placeRoots ∧
      (ownerTy vt address).any Ty.isRefLike = false) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (func)
        target le scopeCount slots (lowerStmt loop (.assignOp op place expression origin) le initial).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have whole := lowerStmt_assignOp_after_rhs (op := op) (org := origin) loop placeRun loadRun valueRun typeRun
  cases current : ls.cur with
  | none =>
    rw [whole]
    simp only [bind_run, emitDef_none _ _ current, emitEffect_none _ _ current]
    exact ⟨upper, ready, fun _ _ => rfl⟩
  | some block =>
    have live : ls.cur.isSome = true := by simp [current]
    have blockBound := ready.current block current
    obtain ⟨next, roots, effects, slotsEq, symbols, finalCurrent, retained⟩ :=
      global_lowerStmt_assignOp_source_witness loop closed placeReplay valueReplay
        source wholeEffect placeRun loadRun valueRun typeRun ready.symbols current blockBound
        ready.roots ready.effects (input live).2.2.2.1 (input live).2.2.2.2
        (input live).1 (input live).2.1 (input live).2.2.1 originBound
    have suffixAdvance := (AdvB.bind (advB_emitDef (.bin op ty old rhs (some origin)))
      (fun result => advB_emitEffect (.store address result (some origin)))) le ls _ _ rfl
    have recipes : (lowerStmt loop (.assignOp op place expression origin) le initial).2.valueRootRecipes =
        ls.valueRootRecipes := by
      rw [whole]
      exact (RecipesUnchangedB.bind (recipesUnchangedB_emitDef (.bin op ty old rhs (some origin)))
        (fun result => recipesUnchangedB_emitEffect (.store address result (some origin)))) le ls
    have growth : upper.vals.size ≤ next.vals.size := by
      rw [ready.roots.valueSize, roots.valueSize, whole]
      exact suffixAdvance.vals
    refine ⟨next, ⟨roots, effects, symbols, ?_, slotsEq.trans ready.slotsEq,
      ready.recipes.prefix recipes retained growth⟩, retained⟩
    intro candidate row
    rw [finalCurrent] at row
    cases row
    rw [whole]
    exact Nat.lt_of_lt_of_le blockBound
      ((AdvB.bind (advB_emitDef (.bin op ty old rhs (some origin)))
        (fun result => advB_emitEffect (.store address result (some origin)))) le ls _ _ rfl).ext.1
private theorem binRecordedType_nonref (env : TyEnv) (operation : BinOp) (type : IntTy) (left right : ValueId) (origin : Option OriginId) :
    (((Op.bin operation type left right origin).resultTy env).toOption.getD (.data .unit)).refLike = false := by
  simp only [Op.resultTy]
  cases first : env.intTy left with
  | error rejection => simp [first, bind, Except.bind, Except.toOption, VTy.refLike, Ty.isRefLike]
  | ok firstType =>
    cases second : env.intTy right with
    | error rejection => simp [first, second, bind, Except.bind, Except.toOption, VTy.refLike, Ty.isRefLike]
    | ok secondType =>
      by_cases comparison : firstType = type ∧ secondType = type <;>
        simp [first, second, comparison, bind, Except.bind, Except.toOption, pure, Except.pure, VTy.refLike, Ty.isRefLike, tyErr]

theorem native_bin_nonref {types : Array (Option VTy)} {before after : LS} {le : LEnv}
    {operation : BinOp} {type : IntTy} {left right value : ValueId} {origin : Option OriginId}
    (native : NativeRows types after) (run : emitDef (.bin operation type left right origin) le before = (value, after))
    (live : before.cur.isSome = true) : valRefLike types value = false := by
  cases current : before.cur with
  | none => simp [current] at live
  | some block =>
    rw [emitDef_run _ _ current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    have row : types[before.vals.size]? = some (some (((Op.bin operation type left right origin).resultTy (tyEnv le before)).toOption.getD (.data .unit))) :=
      native before.vals.size _ (by simp)
    simp only [valRefLike, row]
    exact binRecordedType_nonref _ _ _ _ _ _

end ReplayBuilder

end Goose.Lower.Validation.ReplacementContentFlowSource
