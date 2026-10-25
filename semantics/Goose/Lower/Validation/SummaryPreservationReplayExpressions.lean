import Goose.Lower.Validation.SummaryPreservationReplayValue
import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem expressions {env : PEnv} (expressions : List Expr)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (step : ∀ expression before after roots state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      rpExpr env expression before = .ok (roots, after) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr expression le state).2 next ∧
        ((lowerExpr expression le state).2.cur.isSome = true →
          (lowerExpr expression le state).1 < (lowerExpr expression le state).2.vals.size) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    {before after : RState} (source : rpExprs env expressions before = .ok ((), after)) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExprs expressions le ls).2 next ∧
      ((lowerExprs expressions le ls).2.cur.isSome = true →
        (lowerExprs expressions le ls).1.length = expressions.length ∧
        ∀ value ∈ (lowerExprs expressions le ls).1, value < (lowerExprs expressions le ls).2.vals.size) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  induction expressions generalizing before after ls upper with
  | nil =>
    refine ⟨upper, ready, ?_, fun _ _ => rfl⟩
    intro live
    simp [lowerExprs, pure_run]
  | cons expression rest ih =>
    obtain ⟨roots, middleSource, firstReplay, restReplay⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨middle, middleReady, firstBound, middleRoots⟩ :=
      step expression before middleSource roots ls upper ready firstReplay
    obtain ⟨next, nextReady, tailBounds, nextRoots⟩ := ih middleReady restReplay
    let first := lowerExpr expression le ls
    let tail := lowerExprs rest le first.2
    have whole : lowerExprs (expression :: rest) le ls = (first.1 :: tail.1, tail.2) := by
      simp only [lowerExprs, bind_run, pure_run]
      rfl
    rw [whole]
    refine ⟨next, nextReady, ?_, ?_⟩
    · intro live
      have firstLive : first.2.cur.isSome = true :=
        (dead_lowerExprs rest).live_before (le := le) (before := first.2)
          (after := tail.2) (result := tail.1) rfl live
      obtain ⟨tailLength, tailBound⟩ := tailBounds live
      refine ⟨by simpa using congrArg Nat.succ tailLength, ?_⟩
      intro value member
      rcases List.mem_cons.mp member with firstMember | remaining
      · subst value
        exact Nat.lt_of_lt_of_le (firstBound firstLive)
          (advB_lowerExprs rest le first.2 tail.1 tail.2 rfl).vals
      · exact tailBound value remaining
    · intro index bound
      have growth : upper.vals.size ≤ middle.vals.size := by
        rw [ready.roots.valueSize, middleReady.roots.valueSize]
        exact (advB_lowerExpr expression le ls first.1 first.2 rfl).vals
      exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
