import Goose.Lower.Validation.SummaryPreservationReplayJoin
import Goose.Lower.Validation.SummaryPreservationReplayLoopsBuilder
import Goose.Lower.Validation.SummaryPreservationReplayIfSource

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

theorem ifExpression {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {initial ls : LS} {upper : Prov}
    {env : PEnv} {condition : Expr} {yes no : Core.Block} {conditionValue : ValueId}
    {initialSource conditionState yesState after : RState}
    {conditionRoots yesRoots noRoots sourceRoots : List RootRef} {yesRange noRange : Nat × Nat}
    (type : VTy)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (conditionRun : lowerExpr condition le initial = (conditionValue, ls))
    (conditionBound : ls.cur.isSome = true → conditionValue < ls.vals.size)
    (conditionReplay : rpExpr env condition initialSource = .ok (conditionRoots, conditionState))
    (yesReplay : rpBlockValue env [] yes conditionState = .ok ((yesRoots, yesRange), yesState))
    (noReplay : rpBlockValue env [] no yesState = .ok ((noRoots, noRange), after))
    (source : rpExpr env (.ifE condition yes no) initialSource = .ok (sourceRoots, after))
    (yesChild : ∀ state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock none [] true yes le state).2 next ∧
        ((lowerBlock none [] true yes le state).2.cur.isSome = true →
          ReplayValue func next (lowerBlock none [] true yes le state).2
            (lowerBlock none [] true yes le state).1 yesRoots type) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    (noChild : ∀ state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock none [] true no le state).2 next ∧
        ((lowerBlock none [] true no le state).2.cur.isSome = true →
          ReplayValue func next (lowerBlock none [] true no le state).2
            (lowerBlock none [] true no le state).1 noRoots type) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.ifE condition yes no) le initial).2 next ∧
      ((lowerExpr (.ifE condition yes no) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.ifE condition yes no) le initial).2
          (lowerExpr (.ifE condition yes no) le initial).1 sourceRoots type) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rw [rpExpr_ifE_after_branches conditionReplay yesReplay noReplay] at source
  cases source
  cases current : ls.cur with
  | none =>
    have stopped : lowerExpr (.ifE condition yes no) le initial = (0, ls) := by
      simp only [lowerExpr, bind_run, conditionRun, whenLive_none _ _ _ current]
    rw [stopped]
    exact ⟨upper, ready, by simp [current], fun _ _ => rfl⟩
  | some block =>
    let forked := (fork conditionValue le ls).2
    let yesStart := { forked with cur := some ls.blocks.size }
    have forkReady := ready.loopFork conditionValue (conditionBound (by simp [current]))
    have forkSize : forked.blocks.size = ls.blocks.size + 2 := by
      simp [forked, fork_run _ _ current]
    have yesReady : ReplayBuilder module results vt func target le scopeCount slots yesStart upper := by
      have selected := forkReady.setCur (some ls.blocks.size) (by
        intro candidate row
        have same : candidate = ls.blocks.size := (Option.some.inj row).symm
        subst candidate
        change ls.blocks.size < forked.blocks.size
        rw [forkSize]
        omega)
      simpa only [setCur_run] using selected
    obtain ⟨middle, yesCompleted, yesValue, yesPrefix⟩ := yesChild yesStart upper yesReady
    let yesResult := lowerBlock none [] true yes le yesStart
    have yesGrowth := advB_lowerBlock none [] true yes le yesStart yesResult.1 yesResult.2 rfl
    let noStart := { yesResult.2 with cur := some (ls.blocks.size + 1) }
    have noReady : ReplayBuilder module results vt func target le scopeCount slots noStart middle := by
      have selected := yesCompleted.setCur (some (ls.blocks.size + 1)) (by
        intro candidate row
        cases row
        apply Nat.lt_of_lt_of_le (m := yesStart.blocks.size) _ yesGrowth.ext.1
        change ls.blocks.size + 1 < forked.blocks.size
        rw [forkSize]
        omega)
      simpa only [setCur_run] using selected
    obtain ⟨next, noCompleted, noValue, noPrefix⟩ := noChild noStart middle noReady
    let noResult := lowerBlock none [] true no le noStart
    have noGrowth := advB_lowerBlock none [] true no le noStart noResult.1 noResult.2 rfl
    have firstBound (reachable : yesResult.2.cur.isSome = true) : yesResult.1 < noResult.2.vals.size :=
      Nat.lt_of_lt_of_le (yesValue reachable).bound noGrowth.vals
    have firstRoots (reachable : yesResult.2.cur.isSome = true) :
        rootsAt next.vals yesResult.1 = rootsAt middle.vals yesResult.1 :=
      noPrefix yesResult.1 (by rw [yesCompleted.roots.valueSize]; exact (yesValue reachable).bound)
    obtain ⟨finalUpper, completed, returned, retained⟩ := noCompleted.joinValue
      (unionRoots yesRoots noRoots) type
      (fun destination row => ⟨Nat.lt_of_lt_of_le (yesCompleted.current destination row) noGrowth.ext.1,
        firstBound (by change (lowerBlock none [] true yes le yesStart).2.cur.isSome = true; rw [row]; rfl)⟩)
      (fun destination row => ⟨noCompleted.current destination row, (noValue (by simp [row])).bound⟩)
      (fun reachable => by
        rw [firstRoots reachable]
        exact (yesValue reachable).refined.source_mono
          (fun root member => mem_unionRoots_iff.mpr (Or.inl member)))
      (fun reachable => (noValue reachable).refined.source_mono
        (fun root member => mem_unionRoots_iff.mpr (Or.inr member)))
      (fun nonref reachable => by rw [firstRoots reachable]; exact (yesValue reachable).scalar nonref)
      (fun nonref reachable => (noValue reachable).scalar nonref)
      (value := (Goose.Lower.joinValue yesResult.2.cur yesResult.1 noResult.2.cur noResult.1 le noResult.2).1)
      (final := (Goose.Lower.joinValue yesResult.2.cur yesResult.1 noResult.2.cur noResult.1 le noResult.2).2) rfl
    have whole : lowerExpr (.ifE condition yes no) le initial =
        Goose.Lower.joinValue yesResult.2.cur yesResult.1 noResult.2.cur noResult.1 le noResult.2 := by
      apply lowerExpr_ifE_after_branches conditionRun current
        (forked := forked) (yesBlock := ls.blocks.size) (noBlock := ls.blocks.size + 1)
        (yesValue := yesResult.1) (noValue := noResult.1) (yesLS := yesResult.2) (noLS := noResult.2)
      · simp only [forked, fork_run _ _ current]
      · rfl
      · rfl
    rw [whole]
    refine ⟨finalUpper, completed, returned, ?_⟩
    intro index bound
    have middleGrowth : upper.vals.size ≤ middle.vals.size := by
      rw [yesReady.roots.valueSize, yesCompleted.roots.valueSize]
      exact yesGrowth.vals
    have nextGrowth : middle.vals.size ≤ next.vals.size := by
      rw [noReady.roots.valueSize, noCompleted.roots.valueSize]
      exact noGrowth.vals
    exact (retained index (Nat.lt_of_lt_of_le bound (Nat.le_trans middleGrowth nextGrowth))).trans
      ((noPrefix index (Nat.lt_of_lt_of_le bound middleGrowth)).trans (yesPrefix index bound))

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
