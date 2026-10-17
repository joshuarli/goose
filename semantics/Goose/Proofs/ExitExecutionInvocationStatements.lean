import Goose.Proofs.ExitExecutionInvocationStatementsBase
import Goose.Proofs.ExitExecutionActivationChannelsConstructionHelpers

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem statementInvocation_channels_after_ok (action : EvalM α) (preserves : PreservesActivationChannels action)
    (initial final : ExecutionState) (value : α) (evaluated : action initial = .ok value final)
    (fresh : FreshActivations initial) : ActivationChannelsProjection final = ActivationChannelsProjection initial := by
  have held := preserves initial fresh
  simpa only [evaluated, ActivationChannelsOutcome] using held

elab "statement_channels_head " previous:ident channels:ident config:ident : tactic => do
  let target := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  if target.isForall then
    Lean.Elab.Tactic.evalTactic (← `(tactic| intro))
    return
  if target.getAppFn.isConstOf ``PreservesFresh then
    Lean.Elab.Tactic.evalTactic (← `(tactic| fresh_eval $previous))
    return
  unless target.getAppFn.isConstOf ``PreservesActivationChannels do throwError "expected native channel preservation"
  let action := target.getAppArgs.back!.consumeMData
  if action.isLet || (action.isApp && (action.getAppFn.isLambda || action.getAppFn.isLet)) then
    Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))
    return
  let name := action.getAppFn.constName?.getD .anonymous
  let key := (name.toString.splitOn ".").getLast!
  match key with
  | "bind" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply preservesActivationChannels_bind))
  | "mapM" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply preservesActivationChannels_listMapM))
  | "pure" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_pure _))
  | "ite" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply preservesActivationChannels_conditional))
  | "evalValue" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($channels).value _ _))
  | "evalPlace" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($channels).place _ _))
  | "evalView" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($channels).view _ _))
  | "evalPrintArg" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($channels).printArgument _ _))
  | "loopBody" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($channels).loop _ _ _))
  | "materializeProducer" => Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact preservesActivationChannels_materializeProducer $config _ _ _ _ (($channels).value _ _) (($previous).value _ _)))
  | "materializedDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact preservesActivationChannels_materializedDestination $config _ _ _ _ _ _ _))
  | "ownerDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_ownerDestination $config _ _ _ _ _))
  | "openElementReceiving" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_openElementReceiving $config _ _ _ _ _ _ _))
  | "newDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_newDestination _ _ _ _ _ _ _))
  | "publishCarriers" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_publishCarriers _ _))
  | "bindRoot" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_bindRoot _ _))
  | "truncateOwner" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_truncateOwner _ _ _ _ _))
  | "constructLocal" => do
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply preservesActivationChannels_constructLocal))
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals intro destination))
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals try exact ($channels).build _ _ _))
      Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals exact ($previous).build _ _ _))
  | "liftConstruction" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_liftConstruction _ _))
  | "fault" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_fault _))
  | "freshAct" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_freshAct))
  | "carrierValue" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_of_stateQuery _ (stateQuery_carrierValue _)))
  | "getDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_of_stateQuery _ (stateQuery_getDestination _)))
  | "rootOf" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_of_stateQuery _ (stateQuery_rootOf _ _)))
  | "readLoc" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_of_stateQuery _ (stateQuery_readLoc _ _ _)))
  | "sampledStored" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_of_stateQuery _ (stateQuery_sampledStored _)))
  | "expectInt" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_of_stateQuery _ (stateQuery_expectInt _)))
  | "expectBool" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_of_stateQuery _ (stateQuery_expectBool _)))
  | "arrayLength" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_of_stateQuery _ (stateQuery_arrayLength _)))
  | "sameIntType" => Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_of_stateQuery _ (stateQuery_sameIntType _ _)))
  | _ => Lean.Elab.Tactic.evalTactic (← `(tactic| split))

local macro "statement_channels " previous:ident channels:ident config:ident : tactic => `(tactic|
  repeat' first | assumption | statement_channels_head $previous $channels $config)

private theorem statementReceivePrefix_channels (fuel : Nat) (config : EvalConfig) (previous : EvaluationPreservesFresh fuel config) (channels : EvaluationActivationChannels fuel config) (environment : RuntimeActivation) (locals : List Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (statementInvocation_statementReceivePrefix fuel config environment locals expression origin) := by
  unfold statementInvocation_statementReceivePrefix
  statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config

private theorem globalEnvironmentPrefix_channels (config : EvalConfig) (global : Goose.Core.GlobalId) :
    PreservesActivationChannels (statementInvocation_globalEnvironmentPrefix config global) := by
  unfold statementInvocation_globalEnvironmentPrefix
  have previous := evaluationPreservesFresh_zero config
  have channels := evaluationActivationChannels_zero config
  statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config

private theorem globalValuePrefix_channels (fuel : Nat) (config : EvalConfig) (previous : EvaluationPreservesFresh fuel config) (channels : EvaluationActivationChannels fuel config) (global : Goose.Core.GlobalId) :
    PreservesActivationChannels (statementInvocation_globalValuePrefix fuel config global) := by
  unfold statementInvocation_globalValuePrefix
  have environmentFresh := statementInvocation_globalEnvironmentPrefix_fresh config global
  have environmentChannels := globalEnvironmentPrefix_channels config global
  statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config

partial def statementPrefixChannels (previous channels config : Lean.TSyntax `ident) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let initialSaved ← Lean.Elab.Tactic.saveState
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| first | assumption | rfl))
      return
    catch _ => initialSaved.restore
    let target := (← Lean.Elab.Tactic.getMainTarget).consumeMData
    unless target.isAppOfArity ``Eq 3 do throwError "expected channel projection equality"
    let lhs := target.getAppArgs[1]!.consumeMData
    unless lhs.isAppOfArity ``ActivationChannelsProjection 1 do throwError "expected final channel projection"
    let final := lhs.getAppArgs[0]!
    let saved ← Lean.Elab.Tactic.saveState
    for declaration in (← Lean.getLCtx) do
      let type := (← Lean.instantiateMVars declaration.type).consumeMData
      unless type.isAppOfArity ``Eq 3 do continue
      let rhs := type.getAppArgs[2]!.consumeMData
      unless rhs.isAppOfArity ``ExecutionStep.ok 3 do continue
      unless ← Lean.Meta.isDefEq rhs.getAppArgs[2]! final do continue
      let evidence ← Lean.Elab.Term.exprToSyntax declaration.toExpr
      try
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          refine (statementInvocation_channels_after_ok _ ?_ _ _ _ $evidence ?_).trans ?_))
        Lean.Elab.Tactic.focus (Lean.Elab.Tactic.evalTactic (← `(tactic| statement_channels $previous $channels $config)))
        Lean.Elab.Tactic.focus (statementPrefixFresh previous)
        statementPrefixChannels previous channels config
        return
      catch _ => saved.restore
    throwError "no native successful prefix step reaches this projection"

elab "statement_prefix_channels " previous:ident channels:ident config:ident : tactic =>
  statementPrefixChannels previous channels config

theorem StatementLetNamedPrefix.channels (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId)
    {initial prepared : ExecutionState} {descriptor : LocalVar} {root : Goose.Core.RootInst}
    {named : Option (ResultDescriptor × Nat)}
    (witness : StatementLetNamedPrefix config environment localVar origin initial descriptor root named prepared)
    (fresh : FreshActivations initial) : ActivationChannelsProjection prepared = ActivationChannelsProjection initial := by
  cases witness
  all_goals have previous := evaluationPreservesFresh_zero config
  all_goals have channels := evaluationActivationChannels_zero config
  all_goals statement_prefix_channels previous channels config

theorem StatementOwnerSnapshot.channels (config : EvalConfig) (stored : StoredValue)
    {initial prepared : ExecutionState} {snapshot : Option PendingDestination}
    (witness : StatementOwnerSnapshot stored initial snapshot prepared)
    (fresh : FreshActivations initial) : ActivationChannelsProjection prepared = ActivationChannelsProjection initial := by
  cases witness
  have previous := evaluationPreservesFresh_zero config
  have channels := evaluationActivationChannels_zero config
  statement_prefix_channels previous channels config

theorem StatementLetBuildPrefix.channels (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (channels : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    {initial prepared : ExecutionState} {destination : Nat}
    (witness : StatementLetBuildPrefix fuel config environment localVar expression origin initial destination prepared)
    (fresh : FreshActivations initial) : ActivationChannelsProjection prepared = ActivationChannelsProjection initial := by
  cases witness with
  | actual selected materialized allocated prepared descriptor root named destination namedPrefix materialization allocation preparation =>
      have selectedFresh := namedPrefix.fresh config environment localVar origin fresh
      have selectedChannels := namedPrefix.channels config environment localVar origin fresh
      statement_prefix_channels previous channels config

theorem StatementOwnerBuildPrefix.channels (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (channels : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation)
    {statement : Stmt} {initial prepared : ExecutionState} {snapshot : Option PendingDestination} {destination : Nat}
    (witness : StatementOwnerBuildPrefix fuel config environment statement initial snapshot destination prepared)
    (fresh : FreshActivations initial) : ActivationChannelsProjection prepared = ActivationChannelsProjection initial := by
  cases witness with
  | whole owner expression origin initial located truncated read materialized sampled prepared location stored snapshot destination placeSelected truncation storedSelected materialization snapshotSelected allocation =>
      have materializedFresh : FreshActivations materialized := by statement_prefix_fresh previous
      have materializedChannels : ActivationChannelsProjection materialized = ActivationChannelsProjection initial := by
        statement_prefix_channels previous channels config
      have sampledFresh := snapshotSelected.fresh config stored materializedFresh
      have sampledChannels := (snapshotSelected.channels config stored materializedFresh).trans materializedChannels
      statement_prefix_channels previous channels config
  | append owner expression origin initial located read sampled prepared location stored snapshot destination placeSelected storedSelected snapshotSelected allocation =>
      have readFresh : FreshActivations read := by statement_prefix_fresh previous
      have readChannels : ActivationChannelsProjection read = ActivationChannelsProjection initial := by
        statement_prefix_channels previous channels config
      have sampledFresh := snapshotSelected.fresh config stored readFresh
      have sampledChannels := (snapshotSelected.channels config stored readFresh).trans readChannels
      statement_prefix_channels previous channels config

theorem StatementEachBodyPrefix.channels (fuel : Nat) (config : EvalConfig)
    (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (view : RuntimeView) (current : Nat)
    {initial prepared : ExecutionState} {pre : List (Goose.Core.VarId × Value)}
    (witness : StatementEachBodyPrefix fuel config localVar index byRef view current initial pre prepared)
    (fresh : FreshActivations initial) : ActivationChannelsProjection prepared = ActivationChannelsProjection initial := by
  cases witness
  have previous := evaluationPreservesFresh_zero config
  have channels := evaluationActivationChannels_zero config
  statement_prefix_channels previous channels config

theorem StatementPushBuildPrefix.channels (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (channels : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId)
    {initial prepared : ExecutionState} {snapshot : Option PendingDestination} {destination : Nat}
    (witness : StatementPushBuildPrefix fuel config environment owner expression origin initial snapshot destination prepared)
    (fresh : FreshActivations initial) : ActivationChannelsProjection prepared = ActivationChannelsProjection initial := by
  cases witness with
  | actual located read sampled snapshotted prepared location stored bytes run snapshot destination placeSelected storedSelected runSelected nonfixed snapshotSelected allocation =>
      have sampledFresh : FreshActivations sampled := by statement_prefix_fresh previous
      have sampledChannels : ActivationChannelsProjection sampled = ActivationChannelsProjection initial := by
        statement_prefix_channels previous channels config
      have snapshottedFresh := snapshotSelected.fresh config stored sampledFresh
      have snapshottedChannels := (snapshotSelected.channels config stored sampledFresh).trans sampledChannels
      statement_prefix_channels previous channels config

theorem StatementPushValuePrefix.channels (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (channels : EvaluationActivationChannels fuel config)
    (environment : RuntimeActivation) (owner : Place)
    {initial prepared : ExecutionState}
    (witness : StatementPushValuePrefix fuel config environment owner initial prepared)
    (fresh : FreshActivations initial) : ActivationChannelsProjection prepared = ActivationChannelsProjection initial := by
  cases witness
  statement_prefix_channels previous channels config

theorem StatementInvocationEdge.channels (config : EvalConfig)
    (allFresh : ∀ fuel, EvaluationPreservesFresh fuel config)
    (allChannels : ∀ fuel, EvaluationActivationChannels fuel config)
    {α β : Type} {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared : ExecutionState} (edge : StatementInvocationEdge config parent initial child prepared)
    (fresh : FreshActivations initial) : ActivationChannelsProjection prepared = ActivationChannelsProjection initial := by
  cases edge with
  | assignPlace => rfl
  | assignOpPlace => rfl
  | rebindValue => rfl
  | expression => rfl
  | appendPlace => rfl
  | popPlace => rfl
  | resizePlace => rfl
  | clearPlace => rfl
  | assignWholePlace => rfl
  | ifCondition => rfl
  | «while» => rfl
  | rangeFirst => rfl
  | eachView => rfl
  | appendValuePlace => rfl
  | appendConstructPlace => rfl
  | assertValue => rfl
  | exitValue => rfl
  | letValue fuel environment localVar expression origin initial prepared descriptor root lookup fixed rootSelected =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ rootSelected fresh
      exact preservesActivationChannels_of_stateQuery _ (stateQuery_rootOf _ _)
  | letMaterialize fuel environment localVar expression origin initial prepared descriptor root count named materialize =>
      exact named.channels config environment localVar origin fresh

  | letBuild fuel environment localVar expression origin initial prepared destination setup =>
      exact setup.channels fuel config (allFresh fuel) (allChannels fuel) environment localVar expression origin fresh

  | assignValue fuel environment owner expression origin initial prepared location selected =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ selected fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | assignOpValue fuel environment operation owner expression origin initial prepared old setup =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ setup fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | appendView fuel environment owner view origin initial prepared location selected =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ selected fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | popValue fuel environment owner expression origin initial prepared location selected =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ selected fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | resizeCount fuel environment owner expression fill origin initial prepared location selected =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ selected fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | resizeFill fuel environment owner expression fill origin initial prepared size setup =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ setup fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | assignWholeMaterialize fuel environment owner expression origin initial prepared stored count setup materialize =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ setup fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | assignWholeBuild fuel environment owner expression origin initial prepared destination snapshot setup =>
      exact setup.channels fuel config (allFresh fuel) (allChannels fuel) environment fresh

  | ifYes fuel environment condition yes no origin initial prepared conditionTrue =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ conditionTrue fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | ifNo fuel environment condition yes no origin initial prepared conditionFalse =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ conditionFalse fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | rangeLast fuel environment localVar first last body origin initial prepared start firstValue =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ firstValue fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | rangeLoop fuel environment localVar first last body origin initial prepared ty start stop setup =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ setup fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | eachLoop fuel environment localVar index view byRef body origin initial prepared runtimeView selected =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ selected fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | receiveProduce fuel environment localVars expression origin initial prepared channels setup =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ setup fresh
      exact statementReceivePrefix_channels _ _ previous channels _ _ _ _
  | appendValue fuel environment owner expression origin initial prepared location selected =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ selected fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | appendConstructBuild fuel environment owner expression origin initial prepared destination snapshot setup =>
      exact setup.channels fuel config (allFresh fuel) (allChannels fuel) environment fresh

  | printArgument fuel environment before after argument origin initial prepared parts printed =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ printed fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | whileCondition => rfl
  | whileBody fuel environment condition body initial prepared conditionTrue =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ conditionTrue fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | whileNext fuel environment condition body initial checked prepared flow conditionTrue bodyDone continues =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      have checkedFresh : FreshActivations checked := by
        refine statementInvocation_fresh_after_ok _ ?_ _ _ _ conditionTrue fresh
        fresh_eval previous
      have checkedChannels : ActivationChannelsProjection checked = ActivationChannelsProjection initial := by
        refine statementInvocation_channels_after_ok _ ?_ _ _ _ conditionTrue fresh
        statement_channels previous channels config
      exact (statementInvocation_channels_after_ok _ (channels.loop _ _ _) _ _ _ bodyDone checkedFresh).trans checkedChannels
  | rangeBody => rfl
  | rangeNext fuel environment localVar ty first last body initial prepared flow within bodyDone continues =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ bodyDone fresh
      statement_channels previous channels config <;> try dsimp only <;> statement_channels previous channels config
  | eachBody fuel environment localVar index byRef body view current initial prepared pre setup =>
      exact setup.channels fuel config localVar index byRef view current fresh

  | eachNext fuel environment localVar index byRef body view current initial bound prepared pre flow setup bodyDone continues =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      have boundFresh : FreshActivations bound :=
        setup.fresh fuel config localVar index byRef view current fresh
      have boundChannels := setup.channels fuel config localVar index byRef view current fresh
      exact (statementInvocation_channels_after_ok _ (channels.loop _ _ _) _ _ _ bodyDone boundFresh).trans boundChannels
  | loopBlock => rfl
  | pushPlace => rfl
  | pushBuild fuel environment owner expression origin initial prepared destination snapshot setup =>
      exact setup.channels fuel config (allFresh fuel) (allChannels fuel) environment owner expression origin fresh

  | pushValue fuel environment owner expression origin initial prepared setup =>
      exact setup.channels fuel config (allFresh fuel) (allChannels fuel) environment owner fresh

  | globalValue fuel global globals initial prepared descriptor environment setup fixed =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ setup fresh
      exact globalEnvironmentPrefix_channels _ _
  | globalMaterialize fuel global globals initial prepared descriptor environment count setup nonfixed materialize =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ setup fresh
      exact globalEnvironmentPrefix_channels _ _
  | globalBuild fuel global globals initial prepared allocated descriptor environment destination setup nonfixed materialize allocation =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      have preparedFresh : FreshActivations prepared :=
        statementInvocation_fresh_after_ok _ (statementInvocation_globalEnvironmentPrefix_fresh _ _) _ _ _ setup fresh
      have preparedChannels := statementInvocation_channels_after_ok _ (globalEnvironmentPrefix_channels _ _) _ _ _ setup fresh
      exact (statementInvocation_channels_after_ok _ (preservesActivationChannels_newDestination _ _ _ _ _ _ _) _ _ _ allocation preparedFresh).trans preparedChannels
  | globalNext fuel global globals initial prepared setup =>
      have previous := allFresh fuel
      have channels := allChannels fuel
      refine statementInvocation_channels_after_ok _ ?_ _ _ _ setup fresh
      have valueFresh := statementInvocation_globalValuePrefix_fresh fuel config previous global
      have valueChannels := globalValuePrefix_channels fuel config previous channels global
      statement_channels previous channels config

end Goose.Proofs.ExitExecution
