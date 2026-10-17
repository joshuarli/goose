import Goose.Lower.Validation.SummaryPreservationReplayMutationsEmit
import Goose.Lower.Validation.SummaryPreservationLowerPop

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem pop {env : PEnv} {owner : Place} {origin : OriginId} {type : Ty}
    {initialSource before after : RState} {ownerRoots sourceRoots : List RootRef}
    {initial : LS} {address : ValueId}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (ownerReplay : rpPlace env owner initialSource = .ok (ownerRoots, before))
    (source : rpExpr env (.pop owner origin) initialSource = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (ownerRun : lowerPlace owner le initial = (address, ls))
    (closed : ParameterRootsClosed func) (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) ownerRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.pop owner origin) le initial).2 next ∧
      ((lowerExpr (.pop owner origin) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.pop owner origin) le initial).2
          (lowerExpr (.pop owner origin) le initial).1 sourceRoots (.data type)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rw [rpExpr_pop_after_owner ownerReplay] at source
  cases source
  have whole : lowerExpr (.pop owner origin) le initial = Goose.Lower.emitDef (.pop address (some origin)) le ls := by
    simp only [lowerExpr, bind_run, ownerRun]
  rw [whole]
  apply ready.emitTypedDef_live (.pop address (some origin)) [] (.data type)
  · intro live
    simpa [Op.uses] using (input live).1
  · simpa [Op.origin] using originBound
  · simp [Op.SymbolRefsValid]
  · intro live
    exact (effectStep_pop_refines closed (effectRefinement_empty func before.eff) (input live).2).trans wholeEffect
  · intro live root member
    cases member
  · intros
    rfl

theorem clear {env : PEnv} {owner : Place} {origin : OriginId}
    {initialSource before after : RState} {ownerRoots : List RootRef}
    {initial : LS} {address : ValueId} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (ownerReplay : rpPlace env owner initialSource = .ok (ownerRoots, before))
    (source : rpStmt env (.clear owner origin) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (ownerRun : lowerPlace owner le initial = (address, ls))
    (closed : ParameterRootsClosed func) (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) ownerRoots) :
    ReplayBuilder module results vt func target le scopeCount slots
      (lowerStmt loop (.clear owner origin) le initial).2 upper := by
  have sourceEffect := rpStmt_clear_effect ownerReplay source
  have whole : lowerStmt loop (.clear owner origin) le initial = Goose.Lower.emitEffect (.clear address (some origin)) le ls := by
    simp only [lowerStmt, bind_run, ownerRun]
  rw [whole]
  apply ready.emitEffect_live (.clear address (some origin))
  · intro live
    apply Inst.SymbolsWithin.eff
    · simpa [Effect.uses] using (input live).1
    · simpa [Effect.origin] using originBound
    · trivial
  · intro live
    trivial
  · intro live
    have delta := effectStep_clear_refines (module := module) (vt := vt) (origin := some origin) closed (effectRefinement_empty func before.eff) (input live).2
    rw [← sourceEffect] at delta
    exact delta.trans wholeEffect

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
