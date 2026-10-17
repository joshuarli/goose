import Goose.Lower.Validation.SummaryPreservationReadSource
import Goose.Lower.Validation.SummaryPreservationReplayLiveEmit

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem scalarRead {env : PEnv} {place : Place} {initialSource before after : RState}
    {placeRoots sourceRoots : List RootRef} {initial : LS} {address : ValueId}
    (ty : Ty) (nonref : ty.isRefLike = false)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (closed : ParameterRootsClosed func)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, before))
    (source : rpExpr env (.read place) initialSource = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (placeRun : lowerPlace place le initial = (address, ls))
    (input : ls.cur.isSome = true → address < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) placeRoots)
    (resultType : ls.cur.isSome = true → vt[ls.vals.size]? = some (some (.data ty))) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.read place) le initial).2 next ∧
      ((lowerExpr (.read place) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.read place) le initial).2
          (lowerExpr (.read place) le initial).1 sourceRoots (.data ty)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have sourceEffect := (rpExpr_read_contract placeReplay source).2
  have nodeEffect : EffectRefinement func
      { before.eff with reads := addTargets before.eff.reads (rootsTargets placeRoots) } target := by
    simpa only [sourceEffect] using wholeEffect
  have computedEmpty : ls.cur.isSome = true → rootsOfDef results vt func upper ls.vals.size (.load address) = [] := by
    intro live
    have scalar : valRefLike vt ls.vals.size = false := by
      simp only [valRefLike, resultType live, VTy.refLike, nonref]
    simp only [rootsOfDef, scalar, Bool.false_eq_true, ite_false]
  have whole : lowerExpr (.read place) le initial = Goose.Lower.emitDef (.load address) le ls := by
    simp only [lowerExpr, bind_run, placeRun]
  rw [whole]
  apply ready.emitTypedDef_live (.load address) sourceRoots (.data ty)
  · intro live
    simpa [Op.uses] using (input live).1
  · simp [Op.origin]
  · simp [Op.SymbolRefsValid]
  · intro live
    exact (effectStep_load_refines closed (effectRefinement_empty func before.eff) (input live).2).trans nodeEffect
  · intro live root member
    rw [computedEmpty live] at member
    cases member
  · intro live _
    exact computedEmpty live

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
