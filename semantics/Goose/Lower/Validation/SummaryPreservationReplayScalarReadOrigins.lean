import Goose.Lower.Validation.SummaryPreservationReplayScalarRead

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem scalarReadWithOrigins {env : PEnv} {place : Place} {initialSource before after : RState}
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
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      ((lowerExpr (.read place) le initial).2.cur.isSome = true →
        address < (lowerExpr (.read place) le initial).2.vals.size ∧
        RootsRefine func (rootsAt next.vals address) placeRoots) := by
  obtain ⟨next, completed, value, retained⟩ := ready.scalarRead ty nonref closed placeReplay source wholeEffect placeRun input resultType
  refine ⟨next, completed, value, retained, ?_⟩
  have whole : lowerExpr (.read place) le initial = Goose.Lower.emitDef (.load address) le ls := by
    simp only [lowerExpr, bind_run, placeRun]
  intro live
  rw [whole] at live ⊢
  cases current : ls.cur with
  | none => rw [emitDef_none _ _ current] at live; simp [current] at live
  | some block =>
    have initialLive : ls.cur.isSome = true := by simp [current]
    have addressBound := (input initialLive).1
    constructor
    · rw [emitDef_run _ _ current]
      simpa only [Array.size_push] using Nat.lt_succ_of_lt addressBound
    · rw [retained address (by rw [ready.roots.valueSize]; exact addressBound)]
      exact (input initialLive).2

#print axioms scalarReadWithOrigins

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
