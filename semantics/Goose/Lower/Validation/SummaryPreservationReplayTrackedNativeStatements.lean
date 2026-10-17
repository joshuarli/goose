import Goose.Lower.Validation.SummaryPreservationSourceControlKernelsBounds
import Goose.Lower.Validation.SummaryPreservationSourceEnvironments
import Goose.Lower.Validation.SummaryPreservationReplayTypedStatements
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.SummaryPreservationReturnTransfer

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedStatementsTrackedNative {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env finalEnv : TEnv} {penv : PEnv} {scope start finish : Nat}
    {before after : RState} (loop : Option LoopCtx) (statements : List Stmt) (expected : List RootRef)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyStmts env scope statements start = .ok (finalEnv, finish))
    (replayed : rpStmts penv statements before = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (generatedState : GeneratedBuilderState ls)
    (loopBounds : LoopBuilderTargets loop ls)
    (loopReplay : LoopReplayBounds loop scopeCount ls)
    (native : NativeRows vt (lowerStmts loop statements le ls).2)
    (scopes : env.inExpr = false → ∀ entered ∈ ls.stack, entered < scopeCount)
    (step : ∀ statement, statement ∈ statements → ∀ env1 env2 tn1 tn2 sourceBefore sourceAfter state provenance,
      env1.mod = env.mod → env1.vars = env.vars → env1.impl = env.impl → env1.inExpr = env.inExpr →
      tyStmt env1 scope statement tn1 = .ok (env2, tn2) →
      rpStmt penv statement sourceBefore = .ok ((), sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      state.cur.isSome = true →
      GeneratedBuilderState state → LoopBuilderTargets loop state →
      LoopReplayBounds loop scopeCount state →
      NativeRows vt (lowerStmt loop statement le state).2 →
      (env1.inExpr = false → ∀ entered ∈ state.stack, entered < scopeCount) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerStmt loop statement le state).2 next ∧
        (∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) ∧
        ReturnBoundsPreserved expected state provenance (lowerStmt loop statement le state).2 next) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmts loop statements le ls).2 next ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      ReturnBoundsPreserved expected ls upper (lowerStmts loop statements le ls).2 next := by
  induction statements generalizing env before start ls upper with
  | nil => exact ⟨upper, ready, (fun _ _ => rfl), ReturnBoundsPreserved.refl expected ls upper⟩
  | cons statement rest ih =>
    cases current : ls.cur with
    | none =>
      have stopped : lowerStmts loop (statement :: rest) le ls = ((), ls) := by
        simp [lowerStmts, bind_run, isLive, curBlock_run, current, pure_run]
      rw [stopped]
      exact ⟨upper, ready, (fun _ _ => rfl), ReturnBoundsPreserved.refl expected ls upper⟩
    | some block =>
      obtain ⟨middleEnv, middleCounter, firstTyped, restTyped⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨middleSource, firstReplay, restReplay⟩ := rpStmts_cons_contract replayed
      have firstEffect := effectRefinement_before_of_replay
        (rp_mono_all.2.2.2.2.2.1 penv rest)
        (rp_rebinds_mono_all.2.2.2.2.2.1 penv rest)
        (rp_flags_mono_all.2.2.2.2.2.1 penv rest) restReplay wholeEffect
      have whole : lowerStmts loop (statement :: rest) le ls =
          lowerStmts loop rest le (lowerStmt loop statement le ls).2 := by
        simp [lowerStmts, bind_run, isLive, curBlock_run, current, pure_run]
      have restNative : NativeRows vt (lowerStmts loop rest le (lowerStmt loop statement le ls).2).2 := by
        simpa only [whole] using native
      have firstNative := restNative.of_prefix (types_lowerStmts loop rest le (lowerStmt loop statement le ls).2 _ _ rfl)
      obtain ⟨middle, middleReady, firstRoots, firstTransfer⟩ := step statement (by simp) env middleEnv start middleCounter
        before middleSource ls upper rfl rfl rfl rfl firstTyped firstReplay firstEffect ready (by simp [current]) generatedState loopBounds loopReplay firstNative scopes
      have middleTables := tyStmt_tables statement firstTyped
      have advance := advB_lowerStmt loop statement le ls (lowerStmt loop statement le ls).1 (lowerStmt loop statement le ls).2 rfl
      have middleGenerated : GeneratedBuilderState (lowerStmt loop statement le ls).2 :=
        generatedState.lowerStmt loop statement loopBounds (rfl : lowerStmt loop statement le ls =
          ((lowerStmt loop statement le ls).1, (lowerStmt loop statement le ls).2))
      have middleLoopBounds := loopBounds.mono advance.ext.1
      have middleScopes : middleEnv.inExpr = false →
          ∀ entered ∈ (lowerStmt loop statement le ls).2.stack, entered < scopeCount := by
        intro outside
        rw [advance.stack]
        exact scopes ((source_statement_inExpr statement firstTyped).symm.trans outside)
      obtain ⟨next, completed, nextRoots, nextTransfer⟩ := ih middleReady restTyped restReplay
        middleGenerated middleLoopBounds (loopReplay.mono advance) restNative middleScopes
        (fun child member env1 env2 tn1 tn2 sourceBefore sourceAfter state provenance moduleEq variablesEq implEq modeEq =>
          step child (List.mem_cons_of_mem _ member) env1 env2 tn1 tn2 sourceBefore sourceAfter state provenance
            (moduleEq.trans middleTables.1) (variablesEq.trans middleTables.2.1)
            (implEq.trans middleTables.2.2) (modeEq.trans (source_statement_inExpr statement firstTyped)))
      rw [whole]
      refine ⟨next, completed, ?_, firstTransfer.trans nextTransfer⟩
      intro index bound
      have growth : upper.vals.size ≤ middle.vals.size := by
        rw [ready.roots.valueSize, middleReady.roots.valueSize]
        exact (advB_lowerStmt loop statement le ls _ _ rfl).vals
      exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (firstRoots index bound)

#print axioms typedStatementsTrackedNative

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
