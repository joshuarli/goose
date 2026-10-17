import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlSteps
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.SummaryPreservationReplayTrackedNativeStatements

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem globalStatementsOccurrence_of_statement {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
    {siteRoot root : DemandNode} {siteTargets : List BlockId}
    {loop : Option LoopCtx} {scope : ScopeId} {statements : List Stmt} {initial : LS} {upper : Prov}
    (child : ∀ statement, statement ∈ statements → ∀ nextEnv,
      nextEnv.mod = typingEnv.mod → nextEnv.vars = typingEnv.vars →
      nextEnv.impl = typingEnv.impl → nextEnv.inExpr = typingEnv.inExpr → ∀ state provenance,
      GlobalStatementOccurrenceReplayAt nextEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
        loop scope statement state provenance) :
    GlobalStatementsOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
      loop root scope statements initial upper := by
  intro source origins output start finish before after typed replay ceiling scopes stack ready sites targetBounds
    generated loopBounds loopReplay counterTyped included native projects continuation
  induction statements generalizing typingEnv before start initial upper with
  | nil =>
    exact ⟨upper, ready, (fun _ _ => rfl), (fun expected => ReturnBoundsPreserved.refl expected _ _), .refl _ _, sites⟩
  | cons statement rest ih =>
    let le := lowerEnv env.mod env.impl.vars returnTypes
    cases current : initial.cur with
    | none =>
      have stopped : lowerStmts loop (statement :: rest) le initial = ((), initial) := by
        simp [lowerStmts, bind_run, isLive, curBlock_run, current, pure_run]
      rw [stopped]
      exact ⟨upper, ready, (fun _ _ => rfl), (fun expected => ReturnBoundsPreserved.refl expected _ _), .refl _ _, sites⟩
    | some block =>
      obtain ⟨middleEnv, middleCounter, firstTyped, restTyped⟩ := (st_bind_ok _ _ _ _).mp typed
      obtain ⟨middleSource, firstReplay, restReplay⟩ := rpStmts_cons_contract replay
      have firstEffect := effectRefinement_before_of_replay
        (rp_mono_all.2.2.2.2.2.1 env rest)
        (rp_rebinds_mono_all.2.2.2.2.2.1 env rest)
        (rp_flags_mono_all.2.2.2.2.2.1 env rest) restReplay ceiling
      have whole : lowerStmts loop (statement :: rest) le initial =
          lowerStmts loop rest le (lowerStmt loop statement le initial).2 := by
        simp [lowerStmts, bind_run, isLive, curBlock_run, current, pure_run]
      have restNative : NativeRows vt (lowerStmts loop rest le (lowerStmt loop statement le initial).2).2 := by
        change NativeRows vt (lowerStmts loop (statement :: rest) le initial).2 at native
        simpa only [whole] using native
      have firstNative := restNative.of_prefix (types_lowerStmts loop rest le (lowerStmt loop statement le initial).2 _ _ rfl)
      have restProjects := projects
      rw [whole] at restProjects
      have firstProjects := restProjects.of_advance
        (advB_lowerStmts loop rest le (lowerStmt loop statement le initial).2 _ _ rfl)
      have restContinuation := continuation
      rw [whole] at restContinuation
      have firstContinuation := restContinuation.of_advance
        (advB_lowerStmts loop rest le (lowerStmt loop statement le initial).2 _ _ rfl)
      have firstSource : ∃ path, DemandNodeAt siteRoot path (.statement statement) := by
        obtain ⟨outer, outerAt⟩ := source
        obtain ⟨inner, innerAt⟩ := origins statement (by simp)
        exact ⟨outer ++ inner, sourcePath_append outerAt innerAt⟩
      obtain ⟨middle, middleReady, firstRoots, firstTransfer, firstLedger, firstSites⟩ :=
        child statement (by simp) typingEnv rfl rfl rfl rfl initial upper firstSource
          middleEnv start middleCounter before middleSource firstTyped firstReplay firstEffect
          (SourceScopesWithin.stmts_member scopes (by simp)) stack ready sites targetBounds generated
          loopBounds loopReplay counterTyped included firstNative firstProjects firstContinuation
      have middleTables := tyStmt_tables statement firstTyped
      have advance := advB_lowerStmt loop statement le initial _ _ rfl
      have middleGenerated := generated.lowerStmt loop statement loopBounds
        (rfl : lowerStmt loop statement le initial = ((lowerStmt loop statement le initial).1, (lowerStmt loop statement le initial).2))
      have middleScopes : middleEnv.inExpr = false →
          ∀ entered ∈ (lowerStmt loop statement le initial).2.stack, entered < scopeCount := by
        intro outside
        rw [advance.stack]
        exact stack ((source_statement_inExpr statement firstTyped).symm.trans outside)
      have restScopes : SourceScopesWithin scopeCount (stmtsScopes none rest) := by
        apply scopes.of_subset
        intro entered member
        simp only [stmtsScopes, List.mem_append]
        exact Or.inr member
      obtain ⟨next, completed, nextRoots, nextTransfer, nextLedger, nextSites⟩ :=
        ih (typingEnv := middleEnv) (initial := (lowerStmt loop statement le initial).2) (upper := middle) (before := middleSource) (start := middleCounter)
          (fun item member nextEnv moduleEq variablesEq implEq modeEq =>
            child item (List.mem_cons_of_mem _ member) nextEnv
              (moduleEq.trans middleTables.1) (variablesEq.trans middleTables.2.1)
              (implEq.trans middleTables.2.2) (modeEq.trans (source_statement_inExpr statement firstTyped)))
          (fun item member => origins item (List.mem_cons_of_mem _ member))
          restTyped restReplay restScopes middleScopes middleReady firstSites
          (targetBounds.mono advance.ext) middleGenerated (loopBounds.mono advance.ext.1)
          (loopReplay.mono advance) restNative restProjects restContinuation
      have firstGrowth : upper.vals.size ≤ middle.vals.size := by
        rw [ready.roots.valueSize, middleReady.roots.valueSize]
        exact advance.vals
      have nextGrowth : middle.vals.size ≤ next.vals.size := by
        rw [middleReady.roots.valueSize, completed.roots.valueSize]
        exact (advB_lowerStmts loop rest le (lowerStmt loop statement le initial).2 _ _ rfl).vals
      rw [whole]
      refine ⟨next, completed, ?_, (fun expected => (firstTransfer expected).trans (nextTransfer expected)), ?_, nextSites⟩
      · intro index bound
        exact (nextRoots index (Nat.lt_of_lt_of_le bound firstGrowth)).trans (firstRoots index bound)
      · obtain ⟨path, location⟩ := origins statement (by simp)
        exact ((firstLedger.underRoot location).retained nextGrowth nextRoots).trans nextLedger

#print axioms globalStatementsOccurrence_of_statement

end Goose.Lower.Validation.ReplacementContentFlowSource
