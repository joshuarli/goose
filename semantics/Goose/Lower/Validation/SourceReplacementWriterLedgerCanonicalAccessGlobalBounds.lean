import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessKernel
import Goose.Lower.Validation.SummaryPreservationReplayTypedBounds
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}


theorem canonical_occurrenceReplay_global_bound {typingEnv : TEnv} {env : PEnv} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} (bound : Bound)
    (tables : SourceRootTables typingEnv env)
    (child : ∀ expression, bound = .expr expression ∨ bound = .fromEnd expression → ∀ initial upper,
      CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets expression initial upper) :
    ∀ initial upper, CanonicalGlobalBoundOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets bound initial upper := by
  intro initial upper here sourceCursor start finish before after typed replay ceiling ready sites targets generated native metadata continuation
  cases bound with
  | omitted => exact ⟨upper, ready, by simp [lowerBound, pure_run, Bnd.uses], (fun _ _ => rfl), .refl _ _, sites⟩
  | expr expression | fromEnd expression =>
    obtain ⟨integer, childFinish, childTyped⟩ := tyBound_child typed
    obtain ⟨roots, middle, childReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
    have sourceEq := congrArg Prod.snd ((st_pure_ok _ _ _).mp tail)
    dsimp only at sourceEq
    subst after
    obtain ⟨next, nextReady, value, retained, ledger, finalSites⟩ :=
      child expression (by simp) initial upper (accessChildPresent here 0 rfl) (by
        obtain ⟨path, located⟩ := sourceCursor
        exact ⟨path ++ [0], located.child rfl⟩)
        (.int integer) start childFinish before middle roots childTyped childReplay ceiling ready sites targets generated native metadata continuation
    refine ⟨next, nextReady, ?_, retained, ?_, finalSites⟩
    · intro live
      simpa [lowerBound, bind_run, pure_run, Bnd.uses] using (value live).bound
    · exact ledger.underRoot (accessChildNode 0 rfl)

theorem canonical_accessGlobalBoundScalar {typingEnv : TEnv} {env : PEnv} {returnTypes : List Ty}
    {vt : Array (Option VTy)} {bound : Bound} {start finish : Nat} {initial : LS}
    (tables : SourceRootTables typingEnv env)
    (typed : tyBound typingEnv bound start = .ok ((), finish))
    (generated : GeneratedBuilderState initial)
    (native : NativeRows vt (lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).2)
    (live : (lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true) :
    ∀ value ∈ (lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).1.uses,
      valRefLike vt value = false := by
  cases bound with
  | omitted => simp [lowerBound, pure_run, Bnd.uses]
  | expr expression | fromEnd expression =>
    obtain ⟨integer, childFinish, childTyped⟩ := tyBound_child typed
    have environment : lowerEnv typingEnv.mod typingEnv.vars returnTypes =
        lowerEnv env.mod env.impl.vars returnTypes := by
      rw [← tables.moduleEq, ← tables.variablesEq]
    have expressionNative : NativeRows vt
        (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 := by
      simpa only [lowerBound, bind_run, pure_run] using native
    have expressionLive : (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true := by
      simpa only [lowerBound, bind_run, pure_run] using live
    have scalar := expressionNative.scalar_expression generated childTyped
      (value := (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).1)
      (by rw [environment]) expressionLive rfl
    simpa [lowerBound, bind_run, pure_run, Bnd.uses] using scalar

end Goose.Lower.Validation.SourceReplacementWriterLedger
