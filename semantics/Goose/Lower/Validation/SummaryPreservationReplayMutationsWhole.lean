import Goose.Lower.Validation.SummaryPreservationReplayMutationsOwners
import Goose.Lower.Validation.SummaryPreservationFlags
import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_assignWhole_children {env : PEnv} {owner : Place} {replacement : Expr} {origin : OriginId}
    {initial before after : RState} {ownerRoots : List RootRef}
    (ownerReplay : rpPlace env owner initial = .ok (ownerRoots, before))
    (source : rpStmt env (.assignWhole owner replacement origin) initial = .ok ((), after)) :
    ∃ valueRoots valueState,
      rpExpr env replacement { before with eff := { before.eff with
        reads := addTargets before.eff.reads (rootsTargets ownerRoots),
        shrinks := addTargets before.eff.shrinks (rootsTargets ownerRoots) } } = .ok (valueRoots, valueState) ∧
      after.eff = { valueState.eff with
        writes := addTargets valueState.eff.writes (rootsTargets ownerRoots),
        grows := addTargets valueState.eff.grows (rootsTargets ownerRoots) } := by
  simp only [rpStmt] at source
  obtain ⟨_, _, ownerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  rw [ownerReplay] at ownerSource
  cases ownerSource
  obtain ⟨_, readState, reading, source⟩ := (st_bind_ok _ _ _ _).mp source
  have readEq := congrArg Prod.snd ((st_modify_ok _ _ _).mp reading)
  obtain ⟨_, clearedState, clearing, source⟩ := (st_bind_ok _ _ _ _).mp source
  have clearEq := congrArg Prod.snd ((st_modify_ok _ _ _).mp clearing)
  dsimp at readEq clearEq
  obtain ⟨valueRoots, valueState, valueReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
  refine ⟨valueRoots, valueState, ?_, ?_⟩
  · simpa only [clearEq, readEq] using valueReplay
  · obtain ⟨_, writeState, writing, growing⟩ := (st_bind_ok _ _ _ _).mp source
    have writeEq := congrArg Prod.snd ((st_modify_ok _ _ _).mp writing)
    have growEq := congrArg (fun pair => pair.2.eff) ((st_modify_ok _ _ _).mp growing)
    dsimp at writeEq growEq
    simpa only [writeEq] using growEq

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem assignWhole {env : PEnv} {owner : Place} {replacement : Expr} {origin : OriginId}
    {initialSource before after : RState} {ownerRoots : List RootRef}
    {initial : LS} {address : ValueId} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (ownerReplay : rpPlace env owner initialSource = .ok (ownerRoots, before))
    (source : rpStmt env (.assignWhole owner replacement origin) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (ownerRun : lowerPlace owner le initial = (address, ls))
    (closed : ParameterRootsClosed func) (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) ownerRoots)
    (step : ∀ valueRoots valueState state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      rpExpr env replacement { before with eff := { before.eff with
        reads := addTargets before.eff.reads (rootsTargets ownerRoots),
        shrinks := addTargets before.eff.shrinks (rootsTargets ownerRoots) } } = .ok (valueRoots, valueState) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr replacement le state).2 next ∧
        ((lowerExpr replacement le state).2.cur.isSome = true →
          (lowerExpr replacement le state).1 < (lowerExpr replacement le state).2.vals.size) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmt loop (.assignWhole owner replacement origin) le initial).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨valueRoots, valueState, valueReplay, sourceEffect⟩ := rpStmt_assignWhole_children ownerReplay source
  let cleared := Goose.Lower.emitEffect (.clear address (some origin)) le ls
  let value := lowerExpr replacement le cleared.2
  have clearToValue : EffectRefinement func
      { before.eff with
        reads := addTargets before.eff.reads (rootsTargets ownerRoots),
        shrinks := addTargets before.eff.shrinks (rootsTargets ownerRoots) } valueState.eff := by
    have flags := rpExpr_flags_mono valueReplay
    have rebinds := rpExpr_rebinds_mono valueReplay
    exact (EffectRefinement.refl _ _).source_mono (rpExpr_mono valueReplay).2
      rebinds flags
  have valueToFinal : EffectRefinement func valueState.eff after.eff := by
    rw [sourceEffect]
    refine ⟨fun _ member => member, ?_, ?_, fun _ member => member, fun _ member => member,
      fun h => h, fun h => h, fun h => h⟩
    all_goals exact storageTargets_mono (fun target member => addTargets_left _ _ target member)
  have clearedReady : ReplayBuilder module results vt func target le scopeCount slots cleared.2 upper := by
    apply ready.emitEffect_live (.clear address (some origin))
    · intro live
      apply Inst.SymbolsWithin.eff
      · simpa [Effect.uses] using (input live).1
      · simpa [Effect.origin] using originBound
      · trivial
    · intros
      trivial
    · intro live
      exact (effectStep_clear_refines closed (effectRefinement_empty func before.eff) (input live).2).trans
        (clearToValue.trans (valueToFinal.trans wholeEffect))
  obtain ⟨next, valueReady, valueBound, rootsPrefix⟩ := step valueRoots valueState cleared.2 upper clearedReady valueReplay
  have whole : lowerStmt loop (.assignWhole owner replacement origin) le initial =
      Goose.Lower.emitEffect (.replace address value.1 (some origin)) le value.2 := by
    simp only [lowerStmt, bind_run, ownerRun, cleared, value]
  rw [whole]
  refine ⟨next, ?_, rootsPrefix⟩
  have liveInfo (live : value.2.cur.isSome = true) : ls.cur.isSome = true ∧ address < value.2.vals.size := by
    have clearLive : cleared.2.cur.isSome = true := (dead_lowerExpr replacement).live_before rfl live
    have initialLive : ls.cur.isSome = true := (dead_emitEffect (.clear address (some origin))).live_before rfl clearLive
    have addressBound : address < value.2.vals.size :=
      Nat.lt_of_lt_of_le (input initialLive).1
        (Nat.le_trans (advB_emitEffect (.clear address (some origin)) le ls cleared.1 cleared.2 rfl).vals
          (advB_lowerExpr replacement le cleared.2 value.1 value.2 rfl).vals)
    exact ⟨initialLive, addressBound⟩
  apply valueReady.emitEffect_live (.replace address value.1 (some origin))
  all_goals intro live
  · apply Inst.SymbolsWithin.eff
    · simpa [Effect.uses] using And.intro (liveInfo live).2 (valueBound live)
    · simpa [Effect.origin] using originBound
    · trivial
  · trivial
  · have addressOld : address < upper.vals.size := by rw [ready.roots.valueSize]; exact (input (liveInfo live).1).1
    have roots : RootsRefine func (rootsAt next.vals address) ownerRoots := by
      rw [rootsPrefix address addressOld]
      exact (input (liveInfo live).1).2
    have delta := effectStep_replace_refines (module := module) (vt := vt) (value := value.1)
      (origin := some origin) closed (effectRefinement_empty func valueState.eff) roots
    have cleanup : EffectRefinement func
        { valueState.eff with
          reads := addTargets valueState.eff.reads (rootsTargets ownerRoots),
          writes := addTargets valueState.eff.writes (rootsTargets ownerRoots),
          grows := addTargets valueState.eff.grows (rootsTargets ownerRoots),
          shrinks := addTargets valueState.eff.shrinks (rootsTargets ownerRoots) } after.eff := by
      rw [sourceEffect]
      refine ⟨?_, fun _ member => member, fun _ member => member, ?_, fun _ member => member,
        fun h => h, fun h => h, fun h => h⟩
      · apply storageTargets_mono
        intro target member
        rcases mem_addTargets_iff.mp member with old | added
        · exact old
        · exact (rpExpr_mono valueReplay).2.1 target (addTargets_right _ _ target added)
      · apply storageTargets_mono
        intro target member
        rcases mem_addTargets_iff.mp member with old | added
        · exact old
        · exact (rpExpr_mono valueReplay).2.2.2.2.1 target (addTargets_right _ _ target added)
    exact delta.trans (cleanup.trans wholeEffect)

end ReplayBuilder
end Goose.Lower.Validation.SummaryPreservation
