import Goose.Lower.Validation.SummaryPreservationReplayBuilder
import Goose.Lower.Validation.SummaryPreservationSourceEffectCeiling
import Goose.Lower.Validation.SummaryPreservationStatementReplay
import Goose.Lower.Validation.SourceEnvironment

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedStatements {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env finalEnv : TEnv} {penv : PEnv} {scope start finish : Nat}
    {before after : RState} (loop : Option LoopCtx) (statements : List Stmt)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyStmts env scope statements start = .ok (finalEnv, finish))
    (replayed : rpStmts penv statements before = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (step : ∀ statement, statement ∈ statements → ∀ env1 env2 tn1 tn2 sourceBefore sourceAfter state provenance,
      env1.mod = env.mod → env1.vars = env.vars →
      tyStmt env1 scope statement tn1 = .ok (env2, tn2) →
      rpStmt penv statement sourceBefore = .ok ((), sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      state.cur.isSome = true →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerStmt loop statement le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmts loop statements le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  induction statements generalizing env before start ls upper with
  | nil => exact ⟨upper, ready, fun _ _ => rfl⟩
  | cons statement rest ih =>
    cases current : ls.cur with
    | none =>
      have stopped : lowerStmts loop (statement :: rest) le ls = ((), ls) := by
        simp [lowerStmts, bind_run, isLive, curBlock_run, current, pure_run]
      rw [stopped]
      exact ⟨upper, ready, fun _ _ => rfl⟩
    | some block =>
      obtain ⟨middleEnv, middleCounter, firstTyped, restTyped⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨middleSource, firstReplay, restReplay⟩ := rpStmts_cons_contract replayed
      have firstEffect := effectRefinement_before_of_replay
        (rp_mono_all.2.2.2.2.2.1 penv rest)
        (rp_rebinds_mono_all.2.2.2.2.2.1 penv rest)
        (rp_flags_mono_all.2.2.2.2.2.1 penv rest) restReplay wholeEffect
      obtain ⟨middle, generated, firstRoots⟩ := step statement (by simp) env middleEnv start middleCounter
        before middleSource ls upper rfl rfl firstTyped firstReplay firstEffect ready (by simp [current])
      have middleTables := tyStmt_tables statement firstTyped
      obtain ⟨next, completed, nextRoots⟩ := ih generated restTyped restReplay
        (fun child member env1 env2 tn1 tn2 sourceBefore sourceAfter state provenance moduleEq variablesEq =>
          step child (List.mem_cons_of_mem _ member) env1 env2 tn1 tn2 sourceBefore sourceAfter state provenance
            (moduleEq.trans middleTables.1) (variablesEq.trans middleTables.2.1))
      have whole : lowerStmts loop (statement :: rest) le ls =
          lowerStmts loop rest le (lowerStmt loop statement le ls).2 := by
        simp [lowerStmts, bind_run, isLive, curBlock_run, current, pure_run]
      rw [whole]
      refine ⟨next, completed, ?_⟩
      intro index bound
      have growth : upper.vals.size ≤ middle.vals.size := by
        rw [ready.roots.valueSize, generated.roots.valueSize]
        exact (advB_lowerStmt loop statement le ls _ _ rfl).vals
      exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (firstRoots index bound)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
