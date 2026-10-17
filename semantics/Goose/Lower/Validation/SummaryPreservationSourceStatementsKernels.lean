import Goose.Lower.Validation.SummaryPreservationSourceBlockContracts
import Goose.Lower.Validation.SummaryPreservationReplayTrackedNativeStatements

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem statementsReplay_of_statement {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}
    {loop : Option LoopCtx} {scope : ScopeId} {statements : List Stmt} {initial : LS} {upper : Prov}
    (child : ∀ statement, statement ∈ statements → ∀ nextEnv,
      nextEnv.mod = typingEnv.mod → nextEnv.vars = typingEnv.vars →
      nextEnv.impl = typingEnv.impl → nextEnv.inExpr = typingEnv.inExpr → ∀ state provenance,
      StatementReplayAt nextEnv env results vt target scopeCount loop scope statement state provenance) :
    StatementsReplayAt typingEnv env results vt target scopeCount loop scope statements initial upper := by
  intro output start finish before after typed replay ceiling scopes stack ready generated loopBounds loopReplay native
  apply ready.typedStatementsTrackedNative loop statements (contextTypedResultUpper env.mod env.ctx)
    typed replay ceiling generated loopBounds loopReplay native stack
  intro statement member env1 env2 tn1 tn2 childBefore childAfter state provenance moduleEq variablesEq implEq modeEq
    childTyped childReplay childCeiling childReady live childGenerated childLoop childLoopReplay childNative childStack
  exact child statement member env1 moduleEq variablesEq implEq modeEq state provenance env2 tn1 tn2 childBefore childAfter
    childTyped childReplay childCeiling (SourceScopesWithin.stmts_member scopes member) childStack
    childReady childGenerated childLoop childLoopReplay childNative

#print axioms statementsReplay_of_statement

end Goose.Lower.Validation.SummaryPreservation
