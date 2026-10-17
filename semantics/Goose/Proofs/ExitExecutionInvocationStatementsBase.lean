import Goose.Proofs.ExitExecutionInvocationStatementsDefinitions
import Goose.Proofs.ExitExecutionActivationChannelsHelpers

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem statementInvocation_fresh_after_ok (action : EvalM α) (preserves : PreservesFresh action)
    (initial final : ExecutionState) (value : α) (evaluated : action initial = .ok value final)
    (fresh : FreshActivations initial) : FreshActivations final := by
  have held := preserves initial fresh
  simpa only [evaluated, Goose.Proofs.Exit.stepState] using held

theorem statementInvocation_statementReceivePrefix_fresh (fuel : Nat) (config : EvalConfig) (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation) (locals : List Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (statementInvocation_statementReceivePrefix fuel config environment locals expression origin) := by
  unfold statementInvocation_statementReceivePrefix
  fresh_eval previous <;> dsimp only <;> fresh_eval previous <;> dsimp only <;> fresh_eval previous

theorem statementInvocation_globalEnvironmentPrefix_fresh (config : EvalConfig) (global : Goose.Core.GlobalId) :
    PreservesFresh (statementInvocation_globalEnvironmentPrefix config global) := by
  unfold statementInvocation_globalEnvironmentPrefix
  have previous := evaluationPreservesFresh_zero config
  fresh_eval previous <;> dsimp only <;> fresh_eval previous <;> dsimp only <;> fresh_eval previous

theorem statementInvocation_globalValuePrefix_fresh (fuel : Nat) (config : EvalConfig) (previous : EvaluationPreservesFresh fuel config) (global : Goose.Core.GlobalId) :
    PreservesFresh (statementInvocation_globalValuePrefix fuel config global) := by
  unfold statementInvocation_globalValuePrefix statementInvocation_globalEnvironmentPrefix
  fresh_eval previous <;> dsimp only <;> fresh_eval previous <;> dsimp only <;> fresh_eval previous

partial def statementPrefixFresh (previous : Lean.TSyntax `ident) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| assumption))
      return
    catch _ => pure ()
    let target := (← Lean.Elab.Tactic.getMainTarget).consumeMData
    unless target.isAppOfArity ``FreshActivations 1 do throwError "expected witness freshness: {target}"
    let final := target.getAppArgs[0]!
    let saved ← Lean.Elab.Tactic.saveState
    for declaration in (← Lean.getLCtx) do
      let type := (← Lean.instantiateMVars declaration.type).consumeMData
      unless type.isAppOfArity ``Eq 3 do continue
      let rhs := type.getAppArgs[2]!.consumeMData
      unless rhs.isAppOfArity ``ExecutionStep.ok 3 do continue
      unless ← Lean.Meta.isDefEq rhs.getAppArgs[2]! final do continue
      let evidence ← Lean.Elab.Term.exprToSyntax declaration.toExpr
      try
        Lean.Elab.Tactic.evalTactic (← `(tactic| refine statementInvocation_fresh_after_ok _ ?_ _ _ _ $evidence ?_))
        Lean.Elab.Tactic.focus (Lean.Elab.Tactic.evalTactic (← `(tactic| fresh_eval $previous)))
        statementPrefixFresh previous
        return
      catch _ => saved.restore
    throwError "no actual successful witness step reaches this state"


elab "statement_prefix_fresh " previous:ident : tactic => statementPrefixFresh previous

theorem StatementLetNamedPrefix.fresh (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId)
    {initial prepared : ExecutionState} {descriptor : LocalVar} {root : Goose.Core.RootInst}
    {named : Option (ResultDescriptor × Nat)}
    (witness : StatementLetNamedPrefix config environment localVar origin initial descriptor root named prepared)
    (fresh : FreshActivations initial) : FreshActivations prepared := by
  cases witness
  all_goals have previous := evaluationPreservesFresh_zero config
  all_goals statement_prefix_fresh previous

theorem StatementOwnerSnapshot.fresh (config : EvalConfig) (stored : StoredValue)
    {initial prepared : ExecutionState} {snapshot : Option PendingDestination}
    (witness : StatementOwnerSnapshot stored initial snapshot prepared)
    (fresh : FreshActivations initial) : FreshActivations prepared := by
  cases witness
  have previous := evaluationPreservesFresh_zero config
  statement_prefix_fresh previous

theorem StatementLetBuildPrefix.fresh (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    {initial prepared : ExecutionState} {destination : Nat}
    (witness : StatementLetBuildPrefix fuel config environment localVar expression origin initial destination prepared)
    (fresh : FreshActivations initial) : FreshActivations prepared := by
  cases witness with
  | actual selected materialized allocated prepared descriptor root named destination namedPrefix materialization allocation preparation =>
      have selectedFresh := namedPrefix.fresh config environment localVar origin fresh
      statement_prefix_fresh previous

theorem StatementOwnerBuildPrefix.fresh (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    {statement : Stmt} {initial prepared : ExecutionState} {snapshot : Option PendingDestination} {destination : Nat}
    (witness : StatementOwnerBuildPrefix fuel config environment statement initial snapshot destination prepared)
    (fresh : FreshActivations initial) : FreshActivations prepared := by
  cases witness with
  | whole owner expression origin initial located truncated read materialized sampled prepared location stored snapshot destination placeSelected truncation storedSelected materialization snapshotSelected allocation =>
      have materializedFresh : FreshActivations materialized := by statement_prefix_fresh previous
      have sampledFresh := snapshotSelected.fresh config stored materializedFresh
      statement_prefix_fresh previous
  | append owner expression origin initial located read sampled prepared location stored snapshot destination placeSelected storedSelected snapshotSelected allocation =>
      have readFresh : FreshActivations read := by statement_prefix_fresh previous
      have sampledFresh := snapshotSelected.fresh config stored readFresh
      statement_prefix_fresh previous

theorem StatementEachBodyPrefix.fresh (fuel : Nat) (config : EvalConfig)
    (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (view : RuntimeView) (current : Nat)
    {initial prepared : ExecutionState} {pre : List (Goose.Core.VarId × Value)}
    (witness : StatementEachBodyPrefix fuel config localVar index byRef view current initial pre prepared)
    (fresh : FreshActivations initial) : FreshActivations prepared := by
  cases witness
  have previous := evaluationPreservesFresh_zero config
  statement_prefix_fresh previous

theorem StatementPushBuildPrefix.fresh (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId)
    {initial prepared : ExecutionState} {snapshot : Option PendingDestination} {destination : Nat}
    (witness : StatementPushBuildPrefix fuel config environment owner expression origin initial snapshot destination prepared)
    (fresh : FreshActivations initial) : FreshActivations prepared := by
  cases witness with
  | actual located read sampled snapshotted prepared location stored bytes run snapshot destination placeSelected storedSelected runSelected nonfixed snapshotSelected allocation =>
      have sampledFresh : FreshActivations sampled := by statement_prefix_fresh previous
      have snapshottedFresh := snapshotSelected.fresh config stored sampledFresh
      statement_prefix_fresh previous

theorem StatementPushValuePrefix.fresh (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation) (owner : Place)
    {initial prepared : ExecutionState}
    (witness : StatementPushValuePrefix fuel config environment owner initial prepared)
    (fresh : FreshActivations initial) : FreshActivations prepared := by
  cases witness
  statement_prefix_fresh previous

theorem StatementInvocationEdge.fresh (config : EvalConfig)
    (allFresh : ∀ fuel, EvaluationPreservesFresh fuel config)
    {α β : Type} {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared : ExecutionState} (edge : StatementInvocationEdge config parent initial child prepared)
    (fresh : FreshActivations initial) : FreshActivations prepared := by
  cases edge with
  | assignPlace => exact fresh
  | assignOpPlace => exact fresh
  | rebindValue => exact fresh
  | expression => exact fresh
  | appendPlace => exact fresh
  | popPlace => exact fresh
  | resizePlace => exact fresh
  | clearPlace => exact fresh
  | assignWholePlace => exact fresh
  | ifCondition => exact fresh
  | «while» => exact fresh
  | rangeFirst => exact fresh
  | eachView => exact fresh
  | appendValuePlace => exact fresh
  | appendConstructPlace => exact fresh
  | assertValue => exact fresh
  | exitValue => exact fresh
  | letValue fuel environment localVar expression origin initial prepared descriptor root lookup fixed rootSelected =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ rootSelected fresh
      exact stateQuery_preservesFresh _ (stateQuery_rootOf _ _)
  | letMaterialize fuel environment localVar expression origin initial prepared descriptor root count named materialize =>
      exact named.fresh config environment localVar origin fresh

  | letBuild fuel environment localVar expression origin initial prepared destination setup =>
      exact setup.fresh fuel config (allFresh fuel) environment localVar expression origin fresh

  | assignValue fuel environment owner expression origin initial prepared location selected =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ selected fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | assignOpValue fuel environment operation owner expression origin initial prepared old setup =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ setup fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | appendView fuel environment owner view origin initial prepared location selected =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ selected fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | popValue fuel environment owner expression origin initial prepared location selected =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ selected fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | resizeCount fuel environment owner expression fill origin initial prepared location selected =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ selected fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | resizeFill fuel environment owner expression fill origin initial prepared size setup =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ setup fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | assignWholeMaterialize fuel environment owner expression origin initial prepared stored count setup materialize =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ setup fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | assignWholeBuild fuel environment owner expression origin initial prepared destination snapshot setup =>
      exact setup.fresh fuel config (allFresh fuel) environment fresh

  | ifYes fuel environment condition yes no origin initial prepared conditionTrue =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ conditionTrue fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | ifNo fuel environment condition yes no origin initial prepared conditionFalse =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ conditionFalse fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | rangeLast fuel environment localVar first last body origin initial prepared start firstValue =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ firstValue fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | rangeLoop fuel environment localVar first last body origin initial prepared ty start stop setup =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ setup fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | eachLoop fuel environment localVar index view byRef body origin initial prepared runtimeView selected =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ selected fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | receiveProduce fuel environment localVars expression origin initial prepared channels setup =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ setup fresh
      exact statementInvocation_statementReceivePrefix_fresh _ _ previous _ _ _ _
  | appendValue fuel environment owner expression origin initial prepared location selected =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ selected fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | appendConstructBuild fuel environment owner expression origin initial prepared destination snapshot setup =>
      exact setup.fresh fuel config (allFresh fuel) environment fresh

  | printArgument fuel environment before after argument origin initial prepared parts printed =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ printed fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | whileCondition => exact fresh
  | whileBody fuel environment condition body initial prepared conditionTrue =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ conditionTrue fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | whileNext fuel environment condition body initial checked prepared flow conditionTrue bodyDone continues =>
      have previous := allFresh fuel
      have checkedFresh : FreshActivations checked := by
        refine statementInvocation_fresh_after_ok _ ?_ _ _ _ conditionTrue fresh
        fresh_eval previous
      exact statementInvocation_fresh_after_ok _ (previous.loop _ _ _) _ _ _ bodyDone checkedFresh
  | rangeBody => exact fresh
  | rangeNext fuel environment localVar ty first last body initial prepared flow within bodyDone continues =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ bodyDone fresh
      fresh_eval previous <;> dsimp only <;> fresh_eval previous
  | eachBody fuel environment localVar index byRef body view current initial prepared pre setup =>
      exact setup.fresh fuel config localVar index byRef view current fresh

  | eachNext fuel environment localVar index byRef body view current initial bound prepared pre flow setup bodyDone continues =>
      have previous := allFresh fuel
      have boundFresh : FreshActivations bound :=
        setup.fresh fuel config localVar index byRef view current fresh
      exact statementInvocation_fresh_after_ok _ (previous.loop _ _ _) _ _ _ bodyDone boundFresh
  | loopBlock => exact fresh
  | pushPlace => exact fresh
  | pushBuild fuel environment owner expression origin initial prepared destination snapshot setup =>
      exact setup.fresh fuel config (allFresh fuel) environment owner expression origin fresh

  | pushValue fuel environment owner expression origin initial prepared setup =>
      exact setup.fresh fuel config (allFresh fuel) environment owner fresh

  | globalValue fuel global globals initial prepared descriptor environment setup fixed =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ setup fresh
      exact statementInvocation_globalEnvironmentPrefix_fresh _ _
  | globalMaterialize fuel global globals initial prepared descriptor environment count setup nonfixed materialize =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ setup fresh
      exact statementInvocation_globalEnvironmentPrefix_fresh _ _
  | globalBuild fuel global globals initial prepared allocated descriptor environment destination setup nonfixed materialize allocation =>
      have previous := allFresh fuel
      have preparedFresh : FreshActivations prepared :=
        statementInvocation_fresh_after_ok _ (statementInvocation_globalEnvironmentPrefix_fresh _ _) _ _ _ setup fresh
      exact statementInvocation_fresh_after_ok _ (preservesFresh_newDestination _ _ _ _ _ _ _) _ _ _ allocation preparedFresh
  | globalNext fuel global globals initial prepared setup =>
      have previous := allFresh fuel
      refine statementInvocation_fresh_after_ok _ ?_ _ _ _ setup fresh
      have valueFresh := statementInvocation_globalValuePrefix_fresh fuel config previous global
      fresh_eval previous

end Goose.Proofs.ExitExecution
