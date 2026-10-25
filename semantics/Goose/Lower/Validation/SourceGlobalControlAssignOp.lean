import Goose.Lower.Validation.SourceGlobalControlMutationsCommon

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem global_assignOp_instruction_effects {env : PEnv} {func : Func}
    {op : BinOp} {place : Place} {expression : Expr} {org : OriginId}
    {initial placeState before after : RState} {placeRoots valueRoots : List RootRef}
    {vt : Array (Option VTy)} {loadRoots storeRoots : Prov}
    {address old rhs result : ValueId} {ty : IntTy} {target : Core.Eff}
    (closed : ParameterRootsClosed func)
    (placeReplay : rpPlace env place initial = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before))
    (source : rpStmt env (.assignOp op place expression org) initial = .ok ((), after))
    (loadRefines : RootsRefine (func)
      (rootsAt loadRoots.vals address) placeRoots)
    (storeRefines : RootsRefine (func)
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
    (roots : RootsRefine (func)
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
  have deltas := global_assignOp_instruction_effects (vt := vt) (loadRoots := upper) (storeRoots := upper)
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
  have nextAddress : RootsRefine (func)
      (rootsAt next.vals address) placeRoots := by rw [growth address addressUpper]; exact roots
  have storeDelta := (global_assignOp_instruction_effects (vt := vt) (loadRoots := next)
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

private theorem globalAssignOpAfterRhs {env : PEnv} {func : Func}
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
      RootsRefine (func) (rootsAt upper.vals address) placeRoots ∧
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
    refine ⟨next, ⟨roots, effects, symbols, ?_, slotsEq.trans ready.slotsEq,
      ready.recipes.prefix (by
        rw [whole]
        exact (RecipesUnchangedB.bind (recipesUnchangedB_emitDef (.bin op ty old rhs (some origin)))
          (fun result => recipesUnchangedB_emitEffect (.store address result (some origin)))) le ls) retained (by
        rw [ready.roots.valueSize, roots.valueSize, whole]
        exact ((AdvB.bind (advB_emitDef (.bin op ty old rhs (some origin)))
          (fun result => advB_emitEffect (.store address result (some origin)))) le ls _ _ rfl).vals)⟩, retained⟩
    intro candidate row
    rw [finalCurrent] at row
    cases row
    rw [whole]
    exact Nat.lt_of_lt_of_le blockBound
      ((AdvB.bind (advB_emitDef (.bin op ty old rhs (some origin)))
        (fun result => advB_emitEffect (.store address result (some origin)))) le ls _ _ rfl).ext.1
private theorem globalAssignOpCheckpoint {env : PEnv} {func : Func}
    {op : BinOp} {place : Place} {expression : Expr} {origin : OriginId}
    {initialSource placeState before after : RState} {placeRoots valueRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {initial ls : LS} {le : LEnv} {scopeCount : Nat} {address : ValueId}
    {target : Core.Eff} {slots : Array (List RootRef)} (loop : Option LoopCtx)
    (closed : ParameterRootsClosed func)
    (ready : ReplayBuilder (lower env.mod) results vt (func)
      target le scopeCount slots ls upper)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before))
    (source : rpStmt env (.assignOp op place expression origin) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement (func) after.eff target)
    (placeRun : lowerPlace place le initial = (address, ls))
    (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧
      RootsRefine (func) (rootsAt upper.vals address) placeRoots ∧
      (ownerTy vt address).any Ty.isRefLike = false ∧ valRefLike vt ls.vals.size = false)
    (step : ∀ provenance,
      ReplayBuilder (lower env.mod) results vt (func)
        target le scopeCount slots (Goose.Lower.emitDef (.load address) le ls).2 provenance →
      ∃ next, ReplayBuilder (lower env.mod) results vt (func)
          target le scopeCount slots (lowerExpr expression le (Goose.Lower.emitDef (.load address) le ls).2).2 next ∧
        ((lowerExpr expression le (Goose.Lower.emitDef (.load address) le ls).2).2.cur.isSome = true →
          (lowerExpr expression le (Goose.Lower.emitDef (.load address) le ls).2).1 < (lowerExpr expression le (Goose.Lower.emitDef (.load address) le ls).2).2.vals.size) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (func)
        target le scopeCount slots (lowerStmt loop (.assignOp op place expression origin) le initial).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  let loaded := Goose.Lower.emitDef (.load address) le ls
  let value := lowerExpr expression le loaded.2
  obtain ⟨loadedRoots, loadedReady, loadedValue, loadedPrefix⟩ :=
    ready.emitTypedDef_live (.load address) [] (.data (.int .i64))
      (by intro live; simpa [Op.uses] using (input live).1)
      (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
      (by
        intro live
        exact (global_assignOp_instruction_effects (vt := vt) (loadRoots := upper) (storeRoots := upper)
          (old := ls.vals.size) (rhs := value.1) (result := ls.vals.size) (ty := .i64)
          closed placeReplay valueReplay source
          (input live).2.1 (input live).2.1 (input live).2.2.1 wholeEffect).1)
      (by intro live; simp [rootsOfDef, (input live).2.2.2]; exact RootsRefine.refl _ _)
      (by intro live _; simp [rootsOfDef, (input live).2.2.2])
  obtain ⟨next, valueReady, valueBound, valuePrefix⟩ := step loadedRoots loadedReady
  have loadedBefore := advB_emitDef (.load address) le ls loaded.1 loaded.2 rfl
  have valueBefore := advB_lowerExpr expression le loaded.2 value.1 value.2 rfl
  have initialLive (live : value.2.cur.isSome = true) : ls.cur.isSome = true :=
    (dead_emitDef (.load address)).live_before rfl ((dead_lowerExpr expression).live_before rfl live)
  have oldBound (live : value.2.cur.isSome = true) : loaded.1 < value.2.vals.size :=
    Nat.lt_of_lt_of_le (loadedValue ((dead_lowerExpr expression).live_before rfl live)).bound valueBefore.vals
  have addressBound (live : value.2.cur.isSome = true) : address < value.2.vals.size :=
    Nat.lt_of_lt_of_le (input (initialLive live)).1 (Nat.le_trans loadedBefore.vals valueBefore.vals)
  have actualType : ∃ ty, intTyOf loaded.1 le value.2 = (ty, value.2) := by
    simp only [intTyOf, bind_run]
    generalize row : valTy loaded.1 le value.2 = pair
    have same : pair.2 = value.2 := row ▸ valTy_run loaded.1 le value.2
    obtain ⟨type, state⟩ := pair
    cases type <;> simp_all [pure_run]
    case data type => cases type <;> simp_all [pure_run]
  obtain ⟨type, typeRun⟩ := actualType
  obtain ⟨final, finalReady, finalPrefix⟩ := globalAssignOpAfterRhs loop closed
    valueReady placeReplay valueReplay source wholeEffect placeRun rfl rfl typeRun originBound (by
      intro live
      refine ⟨addressBound live, oldBound live, valueBound live, ?_, (input (initialLive live)).2.2.1⟩
      have old : address < upper.vals.size := by rw [ready.roots.valueSize]; exact (input (initialLive live)).1
      have middle : address < loadedRoots.vals.size := by
        rw [loadedReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le (input (initialLive live)).1 loadedBefore.vals
      rw [valuePrefix address middle, loadedPrefix address old]
      exact (input (initialLive live)).2.1)
  refine ⟨final, finalReady, ?_⟩
  intro index bound
  have loadedBound : index < loadedRoots.vals.size := by
    rw [loadedReady.roots.valueSize]
    exact Nat.lt_of_lt_of_le (ready.roots.valueSize ▸ bound) loadedBefore.vals
  have nextBound : index < next.vals.size := by
    rw [valueReady.roots.valueSize]
    exact Nat.lt_of_lt_of_le (loadedReady.roots.valueSize ▸ loadedBound) valueBefore.vals
  rw [finalPrefix index nextBound, valuePrefix index loadedBound, loadedPrefix index bound]

end ReplayBuilder


private theorem integerType_preserves (value : ValueId) (le : LEnv) (state : LS) :
    ∃ ty, intTyOf value le state = (ty, state) := by
  simp only [intTyOf, bind_run]
  generalize row : valTy value le state = pair
  have same : pair.2 = state := row ▸ valTy_run value le state
  obtain ⟨type, next⟩ := pair
  cases type <;> simp_all [pure_run]
  case data type => cases type <;> simp_all [pure_run]

theorem globalStatementReplay_assignOp {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
    {place : Place} {expression : Expr} (operation : BinOp) (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env)
    (closed : ParameterRootsClosed func)
    (placeChild : GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount place initial upper)
    (valueChild : ∀ provenance, GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression
      (Goose.Lower.emitDef (.load (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).1)
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2).2 provenance) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope (.assignOp operation place expression origin) initial upper := by
  intro output start finish before after typed replay ceiling _sourceScopes _stack ready generated _loopTargets _loopReplay native
  obtain ⟨info, integer, childStart, placeTyped, infoType, valueTyped, _binding, _⟩ := tyStmt_assignOp_children typed
  obtain ⟨placeRoots, placeState, placeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨valueRoots, valueState, valueReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceReplay := replay
  rw [rpStmt_assignOp_after_operands placeReplay valueReplay] at sourceReplay
  have sourceEffect := congrArg (fun pair => pair.2.eff) (Except.ok.inj sourceReplay).symm
  have valueCeiling : EffectRefinement (func) valueState.eff target := by
    apply EffectRefinement.trans (middle := after.eff) ?_ ceiling
    rw [sourceEffect]
    refine ⟨?_, ?_, fun _ h => h, fun _ h => h, fun _ h => h, ?_, fun h => h, fun h => h⟩
    · exact storageTargets_mono (fun t h => addTargets_left _ _ t h)
    · exact storageTargets_mono (fun t h => addTargets_left _ _ t h)
    · intro h
      cases aborts : operation.mayAbort <;> simp [h]
  have placeCeiling := effectRefinement_before_expression valueReplay valueCeiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let address := lowerPlace place le initial
  let loaded := Goose.Lower.emitDef (.load address.1) le address.2
  let value := lowerExpr expression le loaded.2
  have actualType := integerType_preserves loaded.1 le value.2
  obtain ⟨runtimeType, typeRun⟩ := actualType
  have whole := lowerStmt_assignOp_after_rhs (op := operation) (org := origin) loop
    (rfl : lowerPlace place le initial = address) (rfl : Goose.Lower.emitDef (.load address.1) le address.2 = loaded)
    (rfl : lowerExpr expression le loaded.2 = value) typeRun
  have valueNative : NativeRows vt value.2 := by
    rw [whole] at native
    exact (native.of_prefix (types_emitEffect (.store address.1
      (Goose.Lower.emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2).1 (some origin)) le _ _ _ rfl)).of_prefix
      (types_emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2 _ _ rfl)
  have loadNative := valueNative.of_prefix (types_lowerExpr expression le loaded.2 _ _ rfl)
  have placeNative := loadNative.of_prefix (types_emitDef (.load address.1) le address.2 _ _ rfl)
  obtain ⟨middle, placeReady, placeValue, placePrefix⟩ := placeChild info start childStart before placeState placeRoots
    placeTyped placeReplay placeCeiling ready generated placeNative
  obtain ⟨next, completed, nextPrefix⟩ := placeReady.globalAssignOpCheckpoint loop closed
    placeReplay valueReplay replay ceiling rfl (tables.mutation_origin_bound typed) (by
      intro live
      refine ⟨(placeValue live).1, (placeValue live).2, ?_, ?_⟩
      · rw [tables.global_native_place_owner placeNative generated placeTyped rfl live, infoType]
        rfl
      · change valRefLike vt address.2.vals.size = false
        change address.2.cur.isSome = true at live
        cases current : address.2.cur with
        | none => simp only [current, Option.isSome_none, Bool.false_eq_true] at live
        | some block =>
          have actualRun : lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars returnTypes) initial = address := by
            rw [← tables.moduleEq, ← tables.variablesEq]
          obtain ⟨mu, row⟩ := lowerPlace_generated_typed place placeTyped actualRun live generated
          have row' : address.2.vals[address.1]? = some (some (.data (.ref mu (.int integer)))) := by
            simpa only [infoType] using row
          have resultType : (Op.load address.1).resultTy (tyEnv le address.2) = .ok (.data (.int integer)) := by
            simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, row', pure, Except.pure, bind, Except.bind]
          have emitted : loaded.1 = address.2.vals.size ∧ loaded.2.cur = address.2.cur ∧
              loaded.2.vals[loaded.1]? = some (some (.data (.int integer))) ∧
              (∀ old, old < address.2.vals.size → loaded.2.vals[old]? = address.2.vals[old]?) :=
            emitDef_recorded (le := le) current resultType
          have nativeRow := loadNative _ _ emitted.2.2.1
          rw [emitted.1] at nativeRow
          simp only [valRefLike, nativeRow, VTy.refLike, Ty.isRefLike]
    ) (by
      intro provenance childReady
      obtain ⟨next, nextReady, childValue, childPrefix⟩ := valueChild provenance (.int integer) childStart finish
        placeState valueState valueRoots valueTyped valueReplay valueCeiling childReady
        ((generated.lowerPlace place rfl).emitDef (.load address.1) rfl) valueNative
      exact ⟨next, nextReady, fun live => (childValue live).bound, childPrefix⟩)
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old := by
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, placeReady.roots.valueSize]
      exact (advB_lowerPlace place le initial _ _ rfl).vals
    exact (nextPrefix old (Nat.lt_of_lt_of_le bound growth)).trans (placePrefix old bound)
  exact ⟨next, completed, retained, fun expected => global_statement_plain_transfer expected loop typed rfl ready retained⟩


#print axioms globalStatementReplay_assignOp

end Goose.Lower.Validation.SummaryPreservation
