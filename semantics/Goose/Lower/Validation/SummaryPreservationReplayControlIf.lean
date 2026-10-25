import Goose.Lower.Validation.SummaryPreservationReplayControlActions

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

theorem ifStatement {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {initial ls : LS} {upper : Prov}
    {condition : Expr} {yes : Core.Block} {no : Option Core.Block} {conditionValue : ValueId}
    {origin : OriginId} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (conditionRun : lowerExpr condition le initial = (conditionValue, ls))
    (conditionBound : ls.cur.isSome = true → conditionValue < ls.vals.size)
    (yesChild : ∀ state provenance,
      state = { (fork conditionValue le ls).2 with cur := some ls.blocks.size } →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock loop [] false yes le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    (noChild : ∀ body, no = some body → ∀ state provenance,
      state = { (lowerBlock loop [] false yes le
        { (fork conditionValue le ls).2 with cur := some ls.blocks.size }).2 with cur := some (ls.blocks.size + 1) } →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock loop [] false body le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmt loop (.ifS condition yes no origin) le initial).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases current : ls.cur with
  | none =>
    have stopped : lowerStmt loop (.ifS condition yes no origin) le initial = ((), ls) := by
      cases no <;> simp only [lowerStmt, bind_run, conditionRun, whenLive_none _ _ _ current]
    rw [stopped]
    exact ⟨upper, ready, fun _ _ => rfl⟩
  | some block =>
    let forked := (fork conditionValue le ls).2
    let yesStart := { forked with cur := some ls.blocks.size }
    let yesResult := lowerBlock loop [] false yes le yesStart
    have forkReady := ready.loopFork conditionValue (conditionBound (by simp [current]))
    have forkSize : forked.blocks.size = ls.blocks.size + 2 := by simp [forked, fork_run _ _ current]
    have yesReady : ReplayBuilder module results vt func target le scopeCount slots yesStart upper := by
      have selected := forkReady.setCur (some ls.blocks.size) (by
        intro candidate row
        cases row
        change ls.blocks.size < forked.blocks.size
        rw [forkSize]
        omega)
      simpa only [setCur_run] using selected
    obtain ⟨middle, yesCompleted, yesPrefix⟩ := yesChild yesStart upper rfl yesReady
    have yesGrowth := advB_lowerBlock loop [] false yes le yesStart yesResult.1 yesResult.2 rfl
    have joinBound : ls.blocks.size + 1 < yesResult.2.blocks.size := by
      apply Nat.lt_of_lt_of_le (m := yesStart.blocks.size) _ yesGrowth.ext.1
      change ls.blocks.size + 1 < forked.blocks.size
      rw [forkSize]
      omega
    cases other : no with
    | none =>
      have branched := yesCompleted.loopBranch (ls.blocks.size + 1) [] joinBound (by simp) (by simp)
      have selected := branched.setCur (some (ls.blocks.size + 1)) (by
        intro candidate row
        cases row
        exact Nat.lt_of_lt_of_le joinBound (advB_emitTerm (.br (ls.blocks.size + 1) []) le yesResult.2 _ _ rfl).ext.1)
      have whole : lowerStmt loop (.ifS condition yes none origin) le initial =
          Goose.Lower.setCur (some (ls.blocks.size + 1)) le
            (Goose.Lower.emitTerm (.br (ls.blocks.size + 1) []) le yesResult.2).2 := by
        simp only [lowerStmt, bind_run, conditionRun, whenLive_some _ _ _ current,
          fork_run _ _ current, setCur_run, yesResult, yesStart, forked]
      rw [whole]
      exact ⟨middle, selected, yesPrefix⟩
    | some body =>
      let noStart := { yesResult.2 with cur := some (ls.blocks.size + 1) }
      let noResult := lowerBlock loop [] false body le noStart
      have noReady : ReplayBuilder module results vt func target le scopeCount slots noStart middle := by
        have selected := yesCompleted.setCur (some (ls.blocks.size + 1)) (by
          intro candidate row; cases row; exact joinBound)
        simpa only [setCur_run] using selected
      obtain ⟨next, noCompleted, noPrefix⟩ := noChild body other noStart middle rfl noReady
      have noGrowth := advB_lowerBlock loop [] false body le noStart noResult.1 noResult.2 rfl
      have joined := noCompleted.joinArms yesResult.2.cur noResult.2.cur
        (fun last row => Nat.lt_of_lt_of_le (yesCompleted.current last row) noGrowth.ext.1)
        noCompleted.current
      have whole : lowerStmt loop (.ifS condition yes (some body) origin) le initial =
          Goose.Lower.joinArms yesResult.2.cur noResult.2.cur le noResult.2 := by
        simp only [lowerStmt, bind_run, conditionRun, whenLive_some _ _ _ current,
          fork_run _ _ current, setCur_run, curBlock_run, yesResult, noResult, yesStart, noStart, forked]
      rw [whole]
      refine ⟨next, joined, ?_⟩
      intro index bound
      have growth : upper.vals.size ≤ middle.vals.size := by
        rw [ready.roots.valueSize, yesCompleted.roots.valueSize]
        simpa only [yesResult, yesStart, forked, fork_run _ _ current] using yesGrowth.vals
      exact (noPrefix index (Nat.lt_of_lt_of_le bound growth)).trans (yesPrefix index bound)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
