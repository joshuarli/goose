import Goose.Lower.Validation.SummaryPreservationReplayValue

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem bound {env : PEnv} (sourceBound : Bound)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (step : ∀ expression before after roots state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      rpExpr env expression before = .ok (roots, after) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr expression le state).2 next ∧
        ((lowerExpr expression le state).2.cur.isSome = true →
          (lowerExpr expression le state).1 < (lowerExpr expression le state).2.vals.size) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    {before after : RState} (source : rpBound env sourceBound before = .ok ((), after)) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerBound sourceBound le ls).2 next ∧
      ((lowerBound sourceBound le ls).2.cur.isSome = true →
        ∀ value ∈ (lowerBound sourceBound le ls).1.uses, value < (lowerBound sourceBound le ls).2.vals.size) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases sourceBound with
  | omitted =>
    refine ⟨upper, ready, ?_, fun _ _ => rfl⟩
    intro live
    simp [lowerBound, pure_run, Bnd.uses]
  | expr expression | fromEnd expression =>
    obtain ⟨roots, middle, expressionReplay, tail⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨next, nextReady, nextBound, growth⟩ :=
      step expression before middle roots ls upper ready expressionReplay
    simp only [lowerBound, bind_run, pure_run]
    refine ⟨next, nextReady, ?_, growth⟩
    intro live
    simpa [Bnd.uses] using nextBound live

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
