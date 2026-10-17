import Goose.Lower.Validation.SourceGlobalControlLeaves
import Goose.Lower.Validation.SummaryPreservationReplayTrackedNativeStatements

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem globalStatementsReplay_of_statement {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func}
    {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
    {loop : Option LoopCtx} {scope : ScopeId} {statements : List Stmt} {initial : LS} {upper : Prov}
    (inside : typingEnv.inExpr = true)
    (child : ∀ statement, statement ∈ statements → ∀ nextEnv,
      nextEnv.mod = typingEnv.mod → nextEnv.vars = typingEnv.vars →
      nextEnv.impl = typingEnv.impl → nextEnv.inExpr = typingEnv.inExpr → ∀ state provenance,
      GlobalStatementReplayAt nextEnv env results vt func returnTypes slots target scopeCount loop scope statement state provenance) :
    GlobalStatementsReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope statements initial upper := by
  intro output start finish before after typed replay ceiling scopes stack ready generated targets loopReplay native
  obtain ⟨next, completed, retained, _⟩ := ready.typedStatementsTrackedNative loop statements [] typed replay ceiling
    generated targets loopReplay native stack (by
      intro statement member env1 env2 tn1 tn2 childBefore childAfter state provenance moduleEq variablesEq implEq modeEq
        childTyped childReplay childCeiling childReady live childGenerated childTargets childLoop childNative childStack
      obtain ⟨next, completed, retained, transfer⟩ := child statement member env1 moduleEq variablesEq implEq modeEq
        state provenance env2 tn1 tn2 childBefore childAfter childTyped childReplay childCeiling
        (SourceScopesWithin.stmts_member scopes member) childStack childReady childGenerated childTargets childLoop childNative
      exact ⟨next, completed, retained, transfer []⟩)
  exact ⟨next, completed, retained, fun expected =>
    ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize retained
      (returnFrame_lowerStmts loop statements (tyStmts_returnFree statements typed inside) _ _ _ _ rfl)⟩

#print axioms globalStatementsReplay_of_statement

end Goose.Lower.Validation.SummaryPreservation
