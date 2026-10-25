import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlSteps
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.SummaryPreservationSourceControlKernels

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem statementOccurrence_expression {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode}
    {siteTargets : List BlockId} {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}
    {expression : Expr} {origin : OriginId}
    (child : ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper) :
    StatementOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets loop scope
      (.expr expression origin) initial upper := by
  intro source output start finish before after typed replay ceiling scopes stack ready sites targetBounds generated loopBounds loopReplay counterTyped included native projects continuation
  obtain ⟨type, expressionTyped, _⟩ := tyStmt_expr_children typed
  obtain ⟨roots, middle, expressionReplay, returned⟩ := (st_bind_ok _ _ _ _).mp replay
  have stateEq : after = middle := congrArg Prod.snd ((st_pure_ok _ _ _).mp returned)
  subst after
  have expressionAt : DemandNodeAt (.statement (.expr expression origin)) [0] (.expression expression) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have expressionSource : ∃ path, DemandNodeAt siteRoot path (.expression expression) := by
    obtain ⟨path, location⟩ := source
    exact ⟨path ++ [0], sourcePath_append location expressionAt⟩
  obtain ⟨next, completed, value, retained, ledger, finalSites⟩ :=
    child expressionSource type start finish before middle roots expressionTyped expressionReplay ceiling
      ready sites targetBounds generated (by simpa only [lowerStmt, bind_run, pure_run] using native)
      (by simpa only [lowerStmt, bind_run, pure_run] using projects)
      (by simpa only [lowerStmt, bind_run, pure_run] using continuation)
  exact ⟨next, completed, retained, mutation_statement_transfer loop typed rfl ready retained,
    ledger.underRoot expressionAt, finalSites⟩

#print axioms statementOccurrence_expression

end Goose.Lower.Validation.ReplacementContentFlowSource
