import Goose.Proofs.ExitExecutionInvocationStatementsReplay
import Goose.Proofs.ExitExecutionInvocationStatementsLetBuildReplay

import Goose.Proofs.ExitExecutionInvocationStatementsReceiveReplay
import Goose.Proofs.ExitExecutionInvocationStatementsGlobalReplay

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

elab "statement_cleanup_finish" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let boundaries ← statementNativeBoundaries target.getAppArgs[2]!
  for declaration in (← Lean.getLCtx) do
    let type := (← Lean.instantiateMVars declaration.type).consumeMData
    if type.isAppOfArity ``Eq 3 then
      let actual := type.getAppArgs[1]!.consumeMData
      let outcome := type.getAppArgs[2]!.consumeMData
      if actual.getAppFn.isConstOf ``restoreCompletedOwner then
        for boundary in boundaries do
          if boundary.getAppFn.isConstOf ``restoreCompletedOwner then
            let saved ← Lean.Elab.Tactic.saveState
            try
              unless ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEq actual boundary) do
                throwError "different native cleanup call"
              let rewritten := target.replace fun expression => if expression == boundary then some outcome else none
              let equality ← Lean.Meta.withTransparency .all <|
                Lean.Meta.withLocalDeclD `nativeCleanup (← Lean.Meta.inferType boundary) fun result => do
                  let body := target.replace fun expression => if expression == boundary then some result else none
                  let context ← Lean.Meta.mkLambdaFVars #[result] body
                  Lean.Meta.mkAppM ``congrArg #[context, declaration.toExpr]
              let next ← goal.replaceTargetEq rewritten equality
              Lean.Elab.Tactic.replaceMainGoal [next]
              Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))
              return
            catch _ => saved.restore
  throwError "no exact native owner-cleanup equation closes this result"

private theorem statement_assignPlace_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.assignPlace fuel environment owner expression origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.assignPlace fuel environment owner expression origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_assignOpPlace_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (operation : Goose.Core.BinOp) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.assignOpPlace fuel environment operation owner expression origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.assignOpPlace fuel environment operation owner expression origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_rebindValue_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.rebindValue fuel environment localVar expression origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.rebindValue fuel environment localVar expression origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_expression_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.expression fuel environment expression origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.expression fuel environment expression origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_appendPlace_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (view : View) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.appendPlace fuel environment owner view origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.appendPlace fuel environment owner view origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_popPlace_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.popPlace fuel environment owner expression origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.popPlace fuel environment owner expression origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_resizePlace_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (fill : Option Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.resizePlace fuel environment owner expression fill origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.resizePlace fuel environment owner expression fill origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_clearPlace_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.clearPlace fuel environment owner origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.clearPlace fuel environment owner origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_assignWholePlace_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.assignWholePlace fuel environment owner expression origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.assignWholePlace fuel environment owner expression origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_ifCondition_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (yes : Block) (no : Option Block) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.ifCondition fuel environment condition yes no origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.ifCondition fuel environment condition yes no origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  cases no <;> simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_while_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.«while» fuel environment condition body origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.«while» fuel environment condition body origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_rangeFirst_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (first last : Expr) (body : Block) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.rangeFirst fuel environment localVar first last body origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.rangeFirst fuel environment localVar first last body origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_eachView_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (view : View) (byRef : Bool) (body : Block) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.eachView fuel environment localVar index view byRef body origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.eachView fuel environment localVar index view byRef body origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_appendValuePlace_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.appendValuePlace fuel environment owner expression origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.appendValuePlace fuel environment owner expression origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_appendConstructPlace_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.appendConstructPlace fuel environment owner expression origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.appendConstructPlace fuel environment owner expression origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_assertValue_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.assertValue fuel environment expression origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.assertValue fuel environment expression origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_exitValue_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.exitValue fuel environment expression origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.exitValue fuel environment expression origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, escaped]

private theorem statement_letValue_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (descriptor : LocalVar) (root : Goose.Core.RootInst)
      (lookup : environment.vars[localVar]? = some descriptor)
      (fixed : descriptor.ty.nonfixed = false)
      (rootSelected : rootOf environment localVar initial = .ok root prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.letValue fuel environment localVar expression origin initial prepared descriptor root lookup fixed rootSelected) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.letValue fuel environment localVar expression origin initial prepared descriptor root lookup fixed rootSelected _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, lookup, fixed, rootSelected, escaped]

private theorem statement_letMaterialize_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (descriptor : LocalVar) (root : Goose.Core.RootInst) (count : Nat)
      (named : StatementLetNamedPrefix config environment localVar origin initial descriptor root none prepared)
      (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.letMaterialize fuel environment localVar expression origin initial prepared descriptor root count named materialize) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.letMaterialize fuel environment localVar expression origin initial prepared descriptor root count named materialize _ ?_
  all_goals statement_prepare_prefixes
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_letBuild_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (destination : Nat)
      (setup : StatementLetBuildPrefix fuel config environment localVar expression origin initial destination prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.letBuild fuel environment localVar expression origin initial prepared destination setup) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.letBuild fuel environment localVar expression origin initial prepared destination setup _ ?_
  simp only [ExitInvocation.action] at escaped
  exact statementLetBuild_escape fuel config environment localVar expression origin initial prepared destination setup address carriers before escaped

private theorem statement_assignValue_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.assignValue fuel environment owner expression origin initial prepared location selected) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.assignValue fuel environment owner expression origin initial prepared location selected _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, selected, escaped]

private theorem statement_assignOpValue_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (operation : Goose.Core.BinOp)
      (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (old : Goose.Core.IntTy × Int)
      (setup : ((do
        let location ← evalPlace fuel config environment owner
        expectInt (← readLoc fuel config.layout location)) : EvalM (Goose.Core.IntTy × Int)) initial = .ok old prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.assignOpValue fuel environment operation owner expression origin initial prepared old setup) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.assignOpValue fuel environment operation owner expression origin initial prepared old setup _ ?_
  statement_prefix setup
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_appendView_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (view : View)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.appendView fuel environment owner view origin initial prepared location selected) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.appendView fuel environment owner view origin initial prepared location selected _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, selected, escaped]

private theorem statement_popValue_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.popValue fuel environment owner expression origin initial prepared location selected) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.popValue fuel environment owner expression origin initial prepared location selected _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, selected, escaped]

private theorem statement_resizeCount_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (fill : Option Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.resizeCount fuel environment owner expression fill origin initial prepared location selected) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.resizeCount fuel environment owner expression fill origin initial prepared location selected _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, selected, escaped]

private theorem statement_resizeFill_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression fill : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (size : Goose.Core.IntTy × Int)
      (setup : ((do
        let _ ← evalPlace fuel config environment owner
        expectInt (← evalValue fuel config environment expression)) : EvalM (Goose.Core.IntTy × Int)) initial = .ok size prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.resizeFill fuel environment owner expression fill origin initial prepared size setup) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.resizeFill fuel environment owner expression fill origin initial prepared size setup _ ?_
  statement_prefix setup
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_assignWholeMaterialize_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (stored : StoredValue) (count : Nat)
      (setup : ((do
        let location ← evalPlace fuel config environment owner
        truncateOwner fuel config.layout location 0 origin
        let .stored stored ← readLoc fuel config.layout location | fault .shape
        pure stored) : EvalM StoredValue) initial = .ok stored prepared)
      (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.assignWholeMaterialize fuel environment owner expression origin initial prepared stored count setup materialize) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.assignWholeMaterialize fuel environment owner expression origin initial prepared stored count setup materialize _ ?_
  statement_prefix setup
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_assignWholeBuild_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (destination : Nat) (snapshot : Option PendingDestination)
      (setup : StatementOwnerBuildPrefix fuel config environment (.assignWhole owner expression origin) initial snapshot destination prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.assignWholeBuild fuel environment owner expression origin initial prepared destination snapshot setup) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.assignWholeBuild fuel environment owner expression origin initial prepared destination snapshot setup _ ?_
  all_goals statement_prepare_prefixes
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute
  all_goals statement_cleanup_finish

private theorem statement_ifYes_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (yes : Block) (no : Option Block)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (conditionTrue : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool) initial = .ok true prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.ifYes fuel environment condition yes no origin initial prepared conditionTrue) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.ifYes fuel environment condition yes no origin initial prepared conditionTrue _ ?_
  cases no
  all_goals statement_prefix conditionTrue
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_ifNo_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (yes no : Block)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (conditionFalse : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool) initial = .ok false prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.ifNo fuel environment condition yes no origin initial prepared conditionFalse) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.ifNo fuel environment condition yes no origin initial prepared conditionFalse _ ?_
  statement_prefix conditionFalse
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_rangeLast_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (first last : Expr) (body : Block) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (start : Goose.Core.IntTy × Int)
      (firstValue : ((do expectInt (← evalValue fuel config environment first)) : EvalM (Goose.Core.IntTy × Int)) initial = .ok start prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.rangeLast fuel environment localVar first last body origin initial prepared start firstValue) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.rangeLast fuel environment localVar first last body origin initial prepared start firstValue _ ?_
  statement_prefix firstValue
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_rangeLoop_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (first last : Expr) (body : Block) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (ty : Goose.Core.IntTy) (start stop : Int)
      (setup : ((do
        let (ty, first) ← expectInt (← evalValue fuel config environment first)
        let (otherTy, last) ← expectInt (← evalValue fuel config environment last)
        sameIntType ty otherTy
        pure (ty, first, last)) : EvalM (Goose.Core.IntTy × Int × Int)) initial = .ok (ty, start, stop) prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.rangeLoop fuel environment localVar first last body origin initial prepared ty start stop setup) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.rangeLoop fuel environment localVar first last body origin initial prepared ty start stop setup _ ?_
  statement_prefix setup
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_eachLoop_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (index : Option Goose.Core.VarId) (view : View) (byRef : Bool) (body : Block) (origin : Goose.Core.OriginId)
      (initial prepared : ExecutionState) (runtimeView : RuntimeView)
      (selected : evalView fuel config environment view initial = .ok runtimeView prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.eachLoop fuel environment localVar index view byRef body origin initial prepared runtimeView selected) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.eachLoop fuel environment localVar index view byRef body origin initial prepared runtimeView selected _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, selected, escaped]

private theorem statement_receiveProduce_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVars : List Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (channels : List Channel)
      (setup : statementInvocation_statementReceivePrefix fuel config environment localVars expression origin initial = .ok channels prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.receiveProduce fuel environment localVars expression origin initial prepared channels setup) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.receiveProduce fuel environment localVars expression origin initial prepared channels setup _ ?_
  simp only [ExitInvocation.action] at escaped
  exact statementReceiveProduce_escape fuel config environment localVars expression origin initial prepared channels setup address carriers before escaped

private theorem statement_appendValue_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.appendValue fuel environment owner expression origin initial prepared location selected) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.appendValue fuel environment owner expression origin initial prepared location selected _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, bind, pure, selected, escaped]

private theorem statement_appendConstructBuild_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (destination : Nat) (snapshot : Option PendingDestination)
      (setup : StatementOwnerBuildPrefix fuel config environment (.appendConstruct owner expression origin) initial snapshot destination prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.appendConstructBuild fuel environment owner expression origin initial prepared destination snapshot setup) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.appendConstructBuild fuel environment owner expression origin initial prepared destination snapshot setup _ ?_
  all_goals statement_prepare_prefixes
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute
  all_goals statement_cleanup_finish

private theorem statement_printArgument_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (earlier after : List PrintArg) (argument : PrintArg)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (parts : List ByteArray)
      (printed : earlier.mapM (evalPrintArg fuel config environment) initial = .ok parts prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.printArgument fuel environment earlier after argument origin initial prepared parts printed) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.printArgument fuel environment earlier after argument origin initial prepared parts printed _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execStmt, List.mapM_append, List.mapM_cons, bind_assoc, bind, pure, printed, escaped]

private theorem statement_whileCondition_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block)
      (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.whileCondition fuel environment condition body initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.whileCondition fuel environment condition body initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execWhile, bind, pure, escaped]

private theorem statement_whileBody_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block)
      (initial prepared : ExecutionState)
      (conditionTrue : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool) initial = .ok true prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.whileBody fuel environment condition body initial prepared conditionTrue) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.whileBody fuel environment condition body initial prepared conditionTrue _ ?_
  statement_prefix conditionTrue
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_whileNext_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block)
      (initial checked prepared : ExecutionState) (flow : Flow)
      (conditionTrue : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool) initial = .ok true checked)
      (bodyDone : loopBody fuel config environment [] body checked = .ok flow prepared)
      (continues : (∃ value, flow = .normal value) ∨ flow = .continuing)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.whileNext fuel environment condition body initial checked prepared flow conditionTrue bodyDone continues) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.whileNext fuel environment condition body initial checked prepared flow conditionTrue bodyDone continues _ ?_
  rcases continues with ⟨value, rfl⟩ | rfl
  all_goals statement_prefix conditionTrue
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_rangeBody_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (ty : Goose.Core.IntTy) (first last : Int) (body : Block) (initial : ExecutionState)
      (within : first < last)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.rangeBody fuel environment localVar ty first last body initial within) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.rangeBody fuel environment localVar ty first last body initial within _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, execRange, bind, pure, within, escaped]

private theorem statement_rangeNext_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (ty : Goose.Core.IntTy) (first last : Int) (body : Block) (initial prepared : ExecutionState) (flow : Flow)
      (within : first < last)
      (bodyDone : loopBody fuel config environment [(localVar, .int ty first)] body initial = .ok flow prepared)
      (continues : (∃ value, flow = .normal value) ∨ flow = .continuing)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.rangeNext fuel environment localVar ty first last body initial prepared flow within bodyDone continues) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.rangeNext fuel environment localVar ty first last body initial prepared flow within bodyDone continues _ ?_
  rcases continues with ⟨value, rfl⟩ | rfl
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals simp [ExitInvocation.action, execRange, bind, pure, within, bodyDone, escaped]

private theorem statement_eachBody_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block) (view : RuntimeView) (current : Nat)
      (initial prepared : ExecutionState) (pre : List (Goose.Core.VarId × Value))
      (setup : StatementEachBodyPrefix fuel config localVar index byRef view current initial pre prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.eachBody fuel environment localVar index byRef body view current initial prepared pre setup) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.eachBody fuel environment localVar index byRef body view current initial prepared pre setup _ ?_
  all_goals statement_prepare_prefixes
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_eachNext_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block) (view : RuntimeView) (current : Nat)
      (initial bound prepared : ExecutionState) (pre : List (Goose.Core.VarId × Value)) (flow : Flow)
      (setup : StatementEachBodyPrefix fuel config localVar index byRef view current initial pre bound)
      (bodyDone : loopBody fuel config environment pre body bound = .ok flow prepared)
      (continues : (∃ value, flow = .normal value) ∨ flow = .continuing)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.eachNext fuel environment localVar index byRef body view current initial bound prepared pre flow setup bodyDone continues) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.eachNext fuel environment localVar index byRef body view current initial bound prepared pre flow setup bodyDone continues _ ?_
  rcases continues with ⟨value, rfl⟩ | rfl
  all_goals statement_prepare_prefixes
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_loopBlock_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (body : Block) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.loopBlock fuel environment pre body initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.loopBlock fuel environment pre body initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, loopBody, withBreakTarget, mapStepState, bind, pure, escaped]

private theorem statement_pushPlace_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial : ExecutionState)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.pushPlace fuel environment owner expression origin initial) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.pushPlace fuel environment owner expression origin initial _ ?_
  simp only [ExitInvocation.action] at escaped
  simp [ExitInvocation.action, Goose.Construct.pushValue, bind, pure, escaped]

private theorem statement_pushBuild_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (destination : Nat) (snapshot : Option PendingDestination)
      (setup : StatementPushBuildPrefix fuel config environment owner expression origin initial snapshot destination prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.pushBuild fuel environment owner expression origin initial prepared destination snapshot setup) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.pushBuild fuel environment owner expression origin initial prepared destination snapshot setup _ ?_
  all_goals statement_prepare_prefixes
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute
  all_goals statement_cleanup_finish

private theorem statement_pushValue_propagates (config : EvalConfig) (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (setup : StatementPushValuePrefix fuel config environment owner initial prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.pushValue fuel environment owner expression origin initial prepared setup) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.pushValue fuel environment owner expression origin initial prepared setup _ ?_
  all_goals statement_prepare_prefixes
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_globalValue_propagates (config : EvalConfig) (fuel : Nat) (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId)
      (initial prepared : ExecutionState) (descriptor : Global) (environment : RuntimeActivation)
      (setup : statementInvocation_globalEnvironmentPrefix config global initial = .ok (descriptor, environment) prepared)
      (fixed : descriptor.ty.nonfixed = false)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.globalValue fuel global globals initial prepared descriptor environment setup fixed) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.globalValue fuel global globals initial prepared descriptor environment setup fixed _ ?_
  statement_prepare_prefixes
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_globalMaterialize_propagates (config : EvalConfig) (fuel : Nat) (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId)
      (initial prepared : ExecutionState) (descriptor : Global) (environment : RuntimeActivation) (count : Nat)
      (setup : statementInvocation_globalEnvironmentPrefix config global initial = .ok (descriptor, environment) prepared)
      (nonfixed : descriptor.ty.nonfixed = true)
      (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ descriptor.init = some count)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.globalMaterialize fuel global globals initial prepared descriptor environment count setup nonfixed materialize) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.globalMaterialize fuel global globals initial prepared descriptor environment count setup nonfixed materialize _ ?_
  statement_prepare_prefixes
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_globalBuild_propagates (config : EvalConfig) (fuel : Nat) (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId)
      (initial prepared allocated : ExecutionState) (descriptor : Global) (environment : RuntimeActivation) (destination : Nat)
      (setup : statementInvocation_globalEnvironmentPrefix config global initial = .ok (descriptor, environment) prepared)
      (nonfixed : descriptor.ty.nonfixed = true)
      (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ descriptor.init = none)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act descriptor.ty .value descriptor.org none
        (producerCount? ⟨config.module, environment.vars⟩ descriptor.init) prepared = .ok destination allocated)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.globalBuild fuel global globals initial prepared allocated descriptor environment destination setup nonfixed materialize allocation) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.globalBuild fuel global globals initial prepared allocated descriptor environment destination setup nonfixed materialize allocation _ ?_
  statement_prepare_prefixes
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals statement_execute

private theorem statement_globalNext_propagates (config : EvalConfig) (fuel : Nat) (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId)
      (initial prepared : ExecutionState)
      (setup : ((do
        let value ← statementInvocation_globalValuePrefix fuel config global
        bindRoot (.global global) value) : EvalM Unit) initial = .ok () prepared)  :
    StatementInvocationEdge.Propagates config (StatementInvocationEdge.globalNext fuel global globals initial prepared setup) := by
  intro address carriers before escaped
  refine StatementInvocationUnwinds.globalNext fuel global globals initial prepared setup _ ?_
  simp only [ExitInvocation.action] at escaped
  exact statementGlobalNext_escape fuel config global globals initial prepared setup address carriers before escaped

theorem StatementInvocationEdge.propagates (config : EvalConfig)
    {α β : Type} {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared before : ExecutionState} (edge : StatementInvocationEdge config parent initial child prepared)
    (address : ExitAddress) (carriers : List Carrier)
    (escaped : child.action config prepared = .escape address carriers before) :
    StatementInvocationUnwinds config address carriers before edge (parent.action config initial) := by
  cases edge with
  | assignPlace fuel environment owner expression origin initial =>
      exact statement_assignPlace_propagates config fuel environment owner expression origin initial address carriers before escaped
  | assignOpPlace fuel environment operation owner expression origin initial =>
      exact statement_assignOpPlace_propagates config fuel environment operation owner expression origin initial address carriers before escaped
  | rebindValue fuel environment localVar expression origin initial =>
      exact statement_rebindValue_propagates config fuel environment localVar expression origin initial address carriers before escaped
  | expression fuel environment expression origin initial =>
      exact statement_expression_propagates config fuel environment expression origin initial address carriers before escaped
  | appendPlace fuel environment owner view origin initial =>
      exact statement_appendPlace_propagates config fuel environment owner view origin initial address carriers before escaped
  | popPlace fuel environment owner expression origin initial =>
      exact statement_popPlace_propagates config fuel environment owner expression origin initial address carriers before escaped
  | resizePlace fuel environment owner expression fill origin initial =>
      exact statement_resizePlace_propagates config fuel environment owner expression fill origin initial address carriers before escaped
  | clearPlace fuel environment owner origin initial =>
      exact statement_clearPlace_propagates config fuel environment owner origin initial address carriers before escaped
  | assignWholePlace fuel environment owner expression origin initial =>
      exact statement_assignWholePlace_propagates config fuel environment owner expression origin initial address carriers before escaped
  | ifCondition fuel environment condition yes no origin initial =>
      exact statement_ifCondition_propagates config fuel environment condition yes no origin initial address carriers before escaped
  | «while» fuel environment condition body origin initial =>
      exact statement_while_propagates config fuel environment condition body origin initial address carriers before escaped
  | rangeFirst fuel environment localVar first last body origin initial =>
      exact statement_rangeFirst_propagates config fuel environment localVar first last body origin initial address carriers before escaped
  | eachView fuel environment localVar index view byRef body origin initial =>
      exact statement_eachView_propagates config fuel environment localVar index view byRef body origin initial address carriers before escaped
  | appendValuePlace fuel environment owner expression origin initial =>
      exact statement_appendValuePlace_propagates config fuel environment owner expression origin initial address carriers before escaped
  | appendConstructPlace fuel environment owner expression origin initial =>
      exact statement_appendConstructPlace_propagates config fuel environment owner expression origin initial address carriers before escaped
  | assertValue fuel environment expression origin initial =>
      exact statement_assertValue_propagates config fuel environment expression origin initial address carriers before escaped
  | exitValue fuel environment expression origin initial =>
      exact statement_exitValue_propagates config fuel environment expression origin initial address carriers before escaped
  | letValue fuel environment localVar expression origin initial prepared descriptor root lookup fixed rootSelected =>
      exact statement_letValue_propagates config fuel environment localVar expression origin initial prepared descriptor root lookup fixed rootSelected address carriers before escaped
  | letMaterialize fuel environment localVar expression origin initial prepared descriptor root count named materialize =>
      exact statement_letMaterialize_propagates config fuel environment localVar expression origin initial prepared descriptor root count named materialize address carriers before escaped
  | letBuild fuel environment localVar expression origin initial prepared destination setup =>
      exact statement_letBuild_propagates config fuel environment localVar expression origin initial prepared destination setup address carriers before escaped
  | assignValue fuel environment owner expression origin initial prepared location selected =>
      exact statement_assignValue_propagates config fuel environment owner expression origin initial prepared location selected address carriers before escaped
  | assignOpValue fuel environment operation owner expression origin initial prepared old setup =>
      exact statement_assignOpValue_propagates config fuel environment operation owner expression origin initial prepared old setup address carriers before escaped
  | appendView fuel environment owner view origin initial prepared location selected =>
      exact statement_appendView_propagates config fuel environment owner view origin initial prepared location selected address carriers before escaped
  | popValue fuel environment owner expression origin initial prepared location selected =>
      exact statement_popValue_propagates config fuel environment owner expression origin initial prepared location selected address carriers before escaped
  | resizeCount fuel environment owner expression fill origin initial prepared location selected =>
      exact statement_resizeCount_propagates config fuel environment owner expression fill origin initial prepared location selected address carriers before escaped
  | resizeFill fuel environment owner expression fill origin initial prepared size setup =>
      exact statement_resizeFill_propagates config fuel environment owner expression fill origin initial prepared size setup address carriers before escaped
  | assignWholeMaterialize fuel environment owner expression origin initial prepared stored count setup materialize =>
      exact statement_assignWholeMaterialize_propagates config fuel environment owner expression origin initial prepared stored count setup materialize address carriers before escaped
  | assignWholeBuild fuel environment owner expression origin initial prepared destination snapshot setup =>
      exact statement_assignWholeBuild_propagates config fuel environment owner expression origin initial prepared destination snapshot setup address carriers before escaped
  | ifYes fuel environment condition yes no origin initial prepared conditionTrue =>
      exact statement_ifYes_propagates config fuel environment condition yes no origin initial prepared conditionTrue address carriers before escaped
  | ifNo fuel environment condition yes no origin initial prepared conditionFalse =>
      exact statement_ifNo_propagates config fuel environment condition yes no origin initial prepared conditionFalse address carriers before escaped
  | rangeLast fuel environment localVar first last body origin initial prepared start firstValue =>
      exact statement_rangeLast_propagates config fuel environment localVar first last body origin initial prepared start firstValue address carriers before escaped
  | rangeLoop fuel environment localVar first last body origin initial prepared ty start stop setup =>
      exact statement_rangeLoop_propagates config fuel environment localVar first last body origin initial prepared ty start stop setup address carriers before escaped
  | eachLoop fuel environment localVar index view byRef body origin initial prepared runtimeView selected =>
      exact statement_eachLoop_propagates config fuel environment localVar index view byRef body origin initial prepared runtimeView selected address carriers before escaped
  | receiveProduce fuel environment localVars expression origin initial prepared channels setup =>
      exact statement_receiveProduce_propagates config fuel environment localVars expression origin initial prepared channels setup address carriers before escaped
  | appendValue fuel environment owner expression origin initial prepared location selected =>
      exact statement_appendValue_propagates config fuel environment owner expression origin initial prepared location selected address carriers before escaped
  | appendConstructBuild fuel environment owner expression origin initial prepared destination snapshot setup =>
      exact statement_appendConstructBuild_propagates config fuel environment owner expression origin initial prepared destination snapshot setup address carriers before escaped
  | printArgument fuel environment earlier after argument origin initial prepared parts printed =>
      exact statement_printArgument_propagates config fuel environment earlier after argument origin initial prepared parts printed address carriers before escaped
  | whileCondition fuel environment condition body initial =>
      exact statement_whileCondition_propagates config fuel environment condition body initial address carriers before escaped
  | whileBody fuel environment condition body initial prepared conditionTrue =>
      exact statement_whileBody_propagates config fuel environment condition body initial prepared conditionTrue address carriers before escaped
  | whileNext fuel environment condition body initial checked prepared flow conditionTrue bodyDone continues =>
      exact statement_whileNext_propagates config fuel environment condition body initial checked prepared flow conditionTrue bodyDone continues address carriers before escaped
  | rangeBody fuel environment localVar ty first last body initial within =>
      exact statement_rangeBody_propagates config fuel environment localVar ty first last body initial within address carriers before escaped
  | rangeNext fuel environment localVar ty first last body initial prepared flow within bodyDone continues =>
      exact statement_rangeNext_propagates config fuel environment localVar ty first last body initial prepared flow within bodyDone continues address carriers before escaped
  | eachBody fuel environment localVar index byRef body view current initial prepared pre setup =>
      exact statement_eachBody_propagates config fuel environment localVar index byRef body view current initial prepared pre setup address carriers before escaped
  | eachNext fuel environment localVar index byRef body view current initial bound prepared pre flow setup bodyDone continues =>
      exact statement_eachNext_propagates config fuel environment localVar index byRef body view current initial bound prepared pre flow setup bodyDone continues address carriers before escaped
  | loopBlock fuel environment pre body initial =>
      exact statement_loopBlock_propagates config fuel environment pre body initial address carriers before escaped
  | pushPlace fuel environment owner expression origin initial =>
      exact statement_pushPlace_propagates config fuel environment owner expression origin initial address carriers before escaped
  | pushBuild fuel environment owner expression origin initial prepared destination snapshot setup =>
      exact statement_pushBuild_propagates config fuel environment owner expression origin initial prepared destination snapshot setup address carriers before escaped
  | pushValue fuel environment owner expression origin initial prepared setup =>
      exact statement_pushValue_propagates config fuel environment owner expression origin initial prepared setup address carriers before escaped
  | globalValue fuel global globals initial prepared descriptor environment setup fixed =>
      exact statement_globalValue_propagates config fuel global globals initial prepared descriptor environment setup fixed address carriers before escaped
  | globalMaterialize fuel global globals initial prepared descriptor environment count setup nonfixed materialize =>
      exact statement_globalMaterialize_propagates config fuel global globals initial prepared descriptor environment count setup nonfixed materialize address carriers before escaped
  | globalBuild fuel global globals initial prepared allocated descriptor environment destination setup nonfixed materialize allocation =>
      exact statement_globalBuild_propagates config fuel global globals initial prepared _ descriptor environment destination setup nonfixed materialize allocation address carriers before escaped
  | globalNext fuel global globals initial prepared setup =>
      exact statement_globalNext_propagates config fuel global globals initial prepared setup address carriers before escaped

end Goose.Proofs.ExitExecution
