import Goose.Lower.Validation.SummaryPreservationLowerAssignOp
import Goose.Lower.Validation.SummaryPreservationReplayMutationsWhole

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem assignOpAfterRhs {env : PEnv} {context : ContextId}
    {op : BinOp} {place : Place} {expression : Expr} {origin : OriginId}
    {initialSource placeState before after : RState} {placeRoots valueRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {initial placeLS loadedLS ls : LS} {le : LEnv} {scopeCount : Nat}
    {address old rhs : ValueId} {ty : IntTy} {target : Core.Eff}
    {slots : Array (List RootRef)} (loop : Option LoopCtx)
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[context]? = some env.ctx)
    (implLookup : env.mod.impls[env.ctx.impl]? = some env.impl)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl)
      target le scopeCount slots ls upper)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before))
    (source : rpStmt env (.assignOp op place expression origin) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (placeRun : lowerPlace place le initial = (address, placeLS))
    (loadRun : Goose.Lower.emitDef (.load address) le placeLS = (old, loadedLS))
    (valueRun : lowerExpr expression le loadedLS = (rhs, ls))
    (typeRun : intTyOf old le ls = (ty, ls))
    (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧ old < ls.vals.size ∧ rhs < ls.vals.size ∧
      RootsRefine (lowerContextAt env.mod env.ctx env.impl) (rootsAt upper.vals address) placeRoots ∧
      (ownerTy vt address).any Ty.isRefLike = false) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl)
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
      lowerStmt_assignOp_source_witness loop accepted contextLookup implLookup placeReplay valueReplay
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

theorem assignOp {env : PEnv} {context : ContextId}
    {op : BinOp} {place : Place} {expression : Expr} {origin : OriginId}
    {initialSource placeState before after : RState} {placeRoots valueRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {initial ls : LS} {le : LEnv} {scopeCount : Nat} {address : ValueId}
    {target : Core.Eff} {slots : Array (List RootRef)} (loop : Option LoopCtx)
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[context]? = some env.ctx)
    (implLookup : env.mod.impls[env.ctx.impl]? = some env.impl)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl)
      target le scopeCount slots ls upper)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before))
    (source : rpStmt env (.assignOp op place expression origin) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (placeRun : lowerPlace place le initial = (address, ls))
    (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧
      RootsRefine (lowerContextAt env.mod env.ctx env.impl) (rootsAt upper.vals address) placeRoots ∧
      (ownerTy vt address).any Ty.isRefLike = false ∧ valRefLike vt ls.vals.size = false)
    (step : ∀ state provenance,
      ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl)
        target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl)
          target le scopeCount slots (lowerExpr expression le state).2 next ∧
        ((lowerExpr expression le state).2.cur.isSome = true →
          (lowerExpr expression le state).1 < (lowerExpr expression le state).2.vals.size) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl)
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
        exact (assignOp_instruction_effects (vt := vt) (loadRoots := upper) (storeRoots := upper)
          (old := ls.vals.size) (rhs := value.1) (result := ls.vals.size) (ty := .i64)
          accepted contextLookup implLookup placeReplay valueReplay source
          (input live).2.1 (input live).2.1 (input live).2.2.1 wholeEffect).1)
      (by intro live; simp [rootsOfDef, (input live).2.2.2]; exact RootsRefine.refl _ _)
      (by intro live _; simp [rootsOfDef, (input live).2.2.2])
  obtain ⟨next, valueReady, valueBound, valuePrefix⟩ := step loaded.2 loadedRoots loadedReady
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
  obtain ⟨final, finalReady, finalPrefix⟩ := assignOpAfterRhs loop accepted contextLookup implLookup
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

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
