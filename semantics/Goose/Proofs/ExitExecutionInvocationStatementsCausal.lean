import Goose.Proofs.ExitExecutionInvocationStatementsReplay
import Goose.Proofs.ExitExecutionInvocationStatementsNative
import Goose.Proofs.ExitExecutionInvocationStatementsReceiveNative
import Goose.Proofs.ExitExecutionInvocationStatementsLoopBlockInverse
import Goose.Proofs.ExitExecutionInvocationStatementsAssignWholeInverse
import Goose.Proofs.ExitExecutionInvocationStatementsLetCause

import Goose.Proofs.ExitExecutionInvocationStatementsCauses

import Goose.Proofs.ExitExecutionInvocationStatementsGlobalReplay

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

syntax "statement_edge_finish" : tactic

elab_rules : tactic
  | `(tactic| statement_edge_finish) => Lean.Elab.Tactic.withMainContext do
      let saved ← Lean.Elab.Tactic.saveState
      try
        Lean.Elab.Tactic.evalTactic (← `(tactic| first | assumption | statement_execute_simp | (solve | simp_all only [bind, pure, Bool.not_eq_true]; rfl)))
        return
      catch _ => saved.restore
      let target := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      let name := target.getAppFn.constName?.getD .anonymous
      if name == ``StatementLetNamedPrefix then
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          first
            | (solve | apply StatementLetNamedPrefix.absent <;> statement_edge_finish)
            | (solve | apply StatementLetNamedPrefix.receiving <;> statement_edge_finish)
            | (solve | apply StatementLetNamedPrefix.other <;> statement_edge_finish)))
      else if name == ``StatementLetBuildPrefix then
        Lean.Elab.Tactic.evalTactic (← `(tactic| apply StatementLetBuildPrefix.actual))
        Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals statement_edge_finish))
      else if name == ``StatementOwnerSnapshot then
        Lean.Elab.Tactic.evalTactic (← `(tactic| apply StatementOwnerSnapshot.actual))
        Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals statement_edge_finish))
      else if name == ``StatementEachBodyPrefix then
        Lean.Elab.Tactic.evalTactic (← `(tactic| apply StatementEachBodyPrefix.actual))
        Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals statement_edge_finish))
      else if name == ``StatementPushBuildPrefix then
        Lean.Elab.Tactic.evalTactic (← `(tactic| apply StatementPushBuildPrefix.actual))
        Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals statement_edge_finish))
      else if name == ``StatementPushValuePrefix then
        Lean.Elab.Tactic.evalTactic (← `(tactic| apply StatementPushValuePrefix.actual))
        Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals statement_edge_finish))
      else if name == ``StatementOwnerBuildPrefix then
        Lean.Elab.Tactic.evalTactic (← `(tactic| first | apply StatementOwnerBuildPrefix.whole | apply StatementOwnerBuildPrefix.append))
        Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals statement_edge_finish))
      else
        Lean.Elab.Tactic.evalTactic (← `(tactic| first
          | (solve | exact Or.inl ⟨_, by first | assumption | rfl⟩)
          | (solve | exact Or.inr (by first | assumption | rfl))
          | statement_execute))

local macro "statement_edge" : tactic => `(tactic|
  first
    | (solve | apply StatementInvocationEdge.assignPlace <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.assignOpPlace <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.rebindValue <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.expression <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.appendPlace <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.popPlace <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.resizePlace <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.clearPlace <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.assignWholePlace <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.ifCondition <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.«while» <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.rangeFirst <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.eachView <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.appendValuePlace <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.appendConstructPlace <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.assertValue <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.exitValue <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.letValue <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.letMaterialize <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.letBuild <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.assignValue <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.assignOpValue <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.appendView <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.popValue <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.resizeCount <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.resizeFill <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.assignWholeMaterialize <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.assignWholeBuild <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.ifYes <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.ifNo <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.rangeLast <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.rangeLoop <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.eachLoop <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.receiveProduce <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.appendValue <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.appendConstructBuild <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.printArgument <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.whileCondition <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.whileBody <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.whileNext <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.rangeBody <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.rangeNext <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.eachBody <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.eachNext <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.loopBlock <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.pushPlace <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.pushBuild <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.pushValue <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.globalValue <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.globalMaterialize <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.globalBuild <;> statement_edge_finish)
    | (solve | apply StatementInvocationEdge.globalNext <;> statement_edge_finish))

elab "statement_causal_child" : tactic => Lean.Elab.Tactic.withMainContext do
  let saved ← Lean.Elab.Tactic.saveState
  for declaration in (← Lean.getLCtx) do
    let type := (← Lean.instantiateMVars declaration.type).consumeMData
    unless type.isAppOfArity ``Eq 3 do continue
    let lhs := type.getAppArgs[1]!.consumeMData
    let rhs := type.getAppArgs[2]!.consumeMData
    unless rhs.isAppOfArity ``ExecutionStep.escape 4 do continue
    let some name := lhs.getAppFn.constName? | continue
    let arguments := lhs.getAppArgs
    let selection : Option (Lean.Name × Array Nat) :=
      if name == ``evalValue then some (``ExitInvocation.value, #[0, 2, 3])
      else if name == ``evalPlace then some (``ExitInvocation.place, #[0, 2, 3])
      else if name == ``evalView then some (``ExitInvocation.view, #[0, 2, 3])
      else if name == ``evalProduce then some (``ExitInvocation.produce, #[0, 2, 3, 4])
      else if name == ``evalPrintArg then some (``ExitInvocation.printArgument, #[0, 2, 3])
      else if name == ``buildExpr then some (``ExitInvocation.build, #[0, 2, 3, 4])
      else if name == ``execBlock then some (``ExitInvocation.block, #[0, 2, 3, 4, 5])
      else if name == ``execWhile then some (``ExitInvocation.whileLoop, #[0, 2, 3, 4])
      else if name == ``execRange then some (``ExitInvocation.rangeLoop, #[0, 2, 3, 4, 5, 6, 7])
      else if name == ``execEach then some (``ExitInvocation.eachLoop, #[0, 2, 3, 4, 5, 6, 7, 8])
      else if name == ``loopBody then some (``ExitInvocation.loop, #[0, 2, 3, 4])
      else if name == ``initGlobals then some (``ExitInvocation.globals, #[0, 2])
      else none
    let some (constructor, indexes) := selection | continue
    unless indexes.all (fun index => index < arguments.size) do continue
    let invocation := Lean.mkAppN (Lean.mkConst constructor) (indexes.map fun index => arguments[index]!)
    let invocationType ← Lean.Meta.inferType invocation
    unless invocationType.isAppOfArity ``ExitInvocation 1 do continue
    let valueType ← Lean.Elab.Term.exprToSyntax invocationType.getAppArgs[0]!
    let child ← Lean.Elab.Term.exprToSyntax invocation
    let prepared ← Lean.Elab.Term.exprToSyntax arguments.back!
    let before ← Lean.Elab.Term.exprToSyntax rhs.getAppArgs.back!
    let evidence ← Lean.Elab.Term.exprToSyntax declaration.toExpr
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| refine ⟨$valueType, $child, $prepared, $before, ?_, ?_⟩))
      Lean.Elab.Tactic.focus (Lean.Elab.Tactic.evalTactic (← `(tactic| statement_edge)))
      Lean.Elab.Tactic.focus (Lean.Elab.Tactic.evalTactic (← `(tactic| simpa only [ExitInvocation.action] using $evidence)))
      return
    catch _ => saved.restore
  throwError "no actual recursive escape with a native statement edge"

private theorem statement_mapM_escape_inv (action : δ → EvalM γ) (items : List δ)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : items.mapM action initial = .escape address carriers final) :
    ∃ (earlier : List δ) (item : δ) (suffix : List δ) (prepared : ExecutionState) (values : List γ),
      items = earlier ++ item :: suffix ∧ earlier.mapM action initial = .ok values prepared ∧
      action item prepared = .escape address carriers final := by
  induction items generalizing initial with
  | nil => simp [List.mapM_nil, pure] at escaped
  | cons item items previous =>
      simp only [List.mapM_cons] at escaped
      cases first : action item initial with
      | stop reason state | jump target kind state => simp [bind, first] at escaped
      | escape target payload state =>
          simp only [bind, first] at escaped
          cases escaped
          exact ⟨[], item, items, initial, [], rfl, rfl, first⟩
      | ok value middle =>
          cases remaining : items.mapM action middle with
          | stop reason state | jump target kind state | ok values state =>
              simp [bind, first, remaining, pure] at escaped
          | escape target payload state =>
              simp only [bind, first, remaining] at escaped
              cases escaped
              obtain ⟨earlier, failed, suffix, prepared, values, shape, normal, failure⟩ :=
                previous middle remaining
              refine ⟨item :: earlier, failed, suffix, prepared, value :: values, ?_, ?_, failure⟩
              · simp only [List.cons_append, shape]
              · simp [List.mapM_cons, bind, first, normal, pure]

elab "statement_native_escape" : tactic => Lean.Elab.Tactic.withMainContext do
  let saved ← Lean.Elab.Tactic.saveState
  for declaration in (← Lean.getLCtx) do
    let type := (← Lean.instantiateMVars declaration.type).consumeMData
    unless type.isAppOfArity ``Eq 3 do continue
    let lhs := type.getAppArgs[1]!.consumeMData
    let rhs := type.getAppArgs[2]!.consumeMData
    unless lhs.isApp && rhs.isAppOfArity ``ExecutionStep.escape 4 do continue
    let action := lhs.appFn!
    if (action.find? fun expression =>
        [``evalValue, ``evalPlace, ``evalView, ``evalProduce, ``buildExpr, ``evalPrintArg,
          ``ExitInvocation.action, ``execStmt, ``Goose.Construct.pushValue,
          ``execBlock, ``execWhile, ``execRange, ``execEach, ``loopBody, ``initGlobals].any expression.isConstOf).isSome then
      continue
    let actionTerm ← Lean.Elab.Term.exprToSyntax action
    let state ← Lean.Elab.Term.exprToSyntax lhs.appArg!
    let address ← Lean.Elab.Term.exprToSyntax rhs.getAppArgs[1]!
    let carriers ← Lean.Elab.Term.exprToSyntax rhs.getAppArgs[2]!
    let final ← Lean.Elab.Term.exprToSyntax rhs.getAppArgs[3]!
    let evidence ← Lean.Elab.Term.exprToSyntax declaration.toExpr
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        (have native : ProducerNeverEscapes $actionTerm := by
           first
             | exact statementNeverEscapes_receivePrefix _ _ _ _ _ _
             | exact statementNeverEscapes_receiveMaterialize _ _ _ _ _
             | exact statementNeverEscapes_receiveBind _ _
             | statement_never_escapes
         exact False.elim (native $state $address $carriers $final $evidence))))
      return
    catch _ => saved.restore
  throwError "no native escape contradiction"

private theorem statement_print_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (arguments : List PrintArg) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (.print arguments origin) initial =
      .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (.print arguments origin)) initial address carriers := by
  cases printed : arguments.mapM (evalPrintArg fuel config environment) initial with
  | stop reason after | jump target kind after => simp [execStmt, bind, printed] at escaped
  | escape target payload after =>
      simp only [execStmt, bind, printed] at escaped
      cases escaped
      obtain ⟨earlier, argument, later, prepared, parts, shape, normal, failure⟩ :=
        statement_mapM_escape_inv (evalPrintArg fuel config environment) arguments initial address carriers final printed
      subst arguments
      exact ⟨ByteArray, .printArgument fuel environment argument, prepared, final,
        .printArgument fuel environment earlier later argument origin initial prepared parts normal, failure⟩
  | ok parts after =>
      simp only [execStmt, bind, printed] at escaped
      have native : ProducerNeverEscapes (do
        emitStdout (parts.foldl (· ++ ·) ByteArray.empty ++ "\n".toUTF8)
        pure (Flow.normal .unit)) := by
        exact producerNeverEscapes_bind _ _ (statementNeverEscapes_emitStdout _) (fun _ => producerNeverEscapes_pure _)
      exact False.elim (native after address carriers final escaped)

elab "statement_inverse_reduce " equation:term : tactic => Lean.Elab.Tactic.withMainContext do
  let evidence ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm equation none)
  let type := (← Lean.instantiateMVars (← Lean.Meta.inferType evidence)).consumeMData
  unless type.isAppOfArity ``Eq 3 do throwError "expected a native escape equality"
  let lhs := type.getAppArgs[1]!.consumeMData
  let rhs := type.getAppArgs[2]!.consumeMData
  let reduced ← statementExecutionHead lhs
  if reduced == lhs then throwError "native escape is at its result boundary"
  let changed ← Lean.Meta.mkEq reduced rhs
  unless evidence.isFVar do throwError "expected a local native escape equation"
  let goal ← (← Lean.Elab.Tactic.getMainGoal).changeLocalDecl evidence.fvarId! changed (checkDefEq := false)
  Lean.Elab.Tactic.replaceMainGoal [goal]

elab "statement_split_escape " equation:term : tactic => Lean.Elab.Tactic.withMainContext do
  let evidence ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm equation none)
  let type := (← Lean.instantiateMVars (← Lean.Meta.inferType evidence)).consumeMData
  unless type.isAppOfArity ``Eq 3 do throwError "expected a native escape equality"
  let lhs := type.getAppArgs[1]!.consumeMData
  if [``evalValue, ``evalPlace, ``evalView, ``evalProduce, ``buildExpr, ``evalPrintArg,
      ``execBlock, ``execWhile, ``execRange, ``execEach, ``loopBody, ``initGlobals].any lhs.getAppFn.isConstOf then
    throwError "recursive escape requires its actual source-call edge"
  if (lhs.isAppOf ``ite || lhs.isAppOf ``dite) && lhs.getAppNumArgs >= 5 then
    let condition ← Lean.Elab.Term.exprToSyntax lhs.getAppArgs[1]!
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      (by_cases nativeGuard : ($condition)
       all_goals simp only [nativeGuard, ite_true, ite_false] at ($equation))))
    return
  if let some matcher ← Lean.Meta.matchMatcherApp? lhs then
    unless matcher.discrs.isEmpty do
      let discriminant ← statementExecutionDiscriminant matcher.discrs[0]!
      let expression ← Lean.Elab.Term.exprToSyntax discriminant
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        (generalize nativeCase : ($expression) = nativeResult at ($equation)
         cases nativeResult)))
      return
  Lean.Elab.Tactic.evalTactic (← `(tactic| split at ($equation)))

elab "statement_inverse_recorded" : tactic => Lean.Elab.Tactic.withMainContext do
  for declaration in (← Lean.getLCtx) do
    let type := (← Lean.instantiateMVars declaration.type).consumeMData
    unless type.isAppOfArity ``Eq 3 do continue
    let rhs := type.getAppArgs[2]!.consumeMData
    unless rhs.isAppOfArity ``ExecutionStep.escape 4 do continue
    let lhs := type.getAppArgs[1]!.consumeMData
    if [``evalValue, ``evalPlace, ``evalView, ``evalProduce, ``buildExpr, ``evalPrintArg,
        ``execBlock, ``execWhile, ``execRange, ``execEach, ``loopBody, ``initGlobals].any lhs.getAppFn.isConstOf then continue
    let evidence ← Lean.Elab.Term.exprToSyntax declaration.toExpr
    let saved ← Lean.Elab.Tactic.saveState
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| first
        | statement_inverse_reduce ($evidence)
        | statement_split_escape ($evidence)))
      return
    catch _ => saved.restore
  throwError "no recorded native escape prefix remains"

elab "statement_inverse_result " equation:term : tactic => Lean.Elab.Tactic.withMainContext do
  let evidence ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm equation none)
  let type := (← Lean.instantiateMVars (← Lean.Meta.inferType evidence)).consumeMData
  unless type.isAppOfArity ``Eq 3 do throwError "expected a native escape equality"
  let lhs := type.getAppArgs[1]!.consumeMData
  if [``ExecutionStep.ok, ``ExecutionStep.stop, ``ExecutionStep.jump].any lhs.getAppFn.isConstOf then
    Lean.Elab.Tactic.evalTactic (← `(tactic| cases ($equation)))
  else throwError "native escape has not reached a terminal result"

macro "statement_native_contradiction" : tactic => `(tactic|
  simp_all only [producerNeverEscapes_pure, producerNeverEscapes_get, producerNeverEscapes_set,
    producerNeverEscapes_fault, producerNeverEscapes_timeout, producerNeverEscapes_liftConstruction,
    producerNeverEscapes_liftLayout, producerNeverEscapes_liftExcept, producerNeverEscapes_rootOf,
    producerNeverEscapes_getDestination, producerNeverEscapes_getStorage, producerNeverEscapes_readLoc,
    producerNeverEscapes_newDestination, producerNeverEscapes_sampledStored, producerNeverEscapes_carrierValue,
    producerNeverEscapes_completedReceivingDestination, producerNeverEscapes_storedDestination,
    producerNeverEscapes_copyValue, valueNeverEscapes_expectInt, valueNeverEscapes_expectBool,
    valueNeverEscapes_expectRef, valueNeverEscapes_sameIntType, valueNeverEscapes_comparable,
    valueNeverEscapes_arrayLength, valueNeverEscapes_writeLoc, valueNeverEscapes_truncateOwner,
    valueNeverEscapes_bindRoot, valueNeverEscapes_publishCarriers, valueNeverEscapes_renderAny,
    valueNeverEscapes_renderView, statementNeverEscapes_freshAct, statementNeverEscapes_emitStdout,
    statementNeverEscapes_materializedDestination, statementNeverEscapes_ownerDestination,
    statementNeverEscapes_openElementReceiving, statementNeverEscapes_restoreCompletedOwner,
    statementNeverEscapes_publishOwner, statementNeverEscapes_publishElementReceiving,
    statementNeverEscapes_appendFixedValues, statementNeverEscapes_appendRun,
    statementNeverEscapes_currentBreak, statementNeverEscapes_jump, statementNeverEscapes_stop,
    statementNeverEscapes_receivePrefix, statementNeverEscapes_receiveMaterialize, statementNeverEscapes_receiveBind])

elab "statement_causal_results" : tactic => Lean.Elab.Tactic.withMainContext do
  let environment ← Lean.getEnv
  for declaration in (← Lean.getLCtx) do
    let type := (← Lean.instantiateMVars declaration.type).consumeMData
    unless type.isAppOfArity ``Eq 3 do continue
    let lhs := type.getAppArgs[1]!.consumeMData
    let rhs := type.getAppArgs[2]!.consumeMData
    unless lhs.isFVar do continue
    let isConstructor := match environment.find? (rhs.getAppFn.constName?.getD .anonymous) with
      | some (.ctorInfo _) => true
      | _ => false
    unless isConstructor do continue
    let valueType ← Lean.Meta.inferType lhs
    unless valueType.isConstOf ``Bool || valueType.isConstOf ``Flow do continue
    let evidence ← Lean.Elab.Term.exprToSyntax declaration.toExpr
    Lean.Elab.Tactic.evalTactic (← `(tactic| cases ($evidence)))
    return
  throwError "no native flow or boolean equation remains"

elab "statement_causal_booleans" : tactic => Lean.Elab.Tactic.withMainContext do
  for declaration in (← Lean.getLCtx) do
    let type ← Lean.instantiateMVars declaration.type
    if let some negated ← Lean.Meta.matchNot? type then
      let condition := negated.consumeMData
      if condition.isAppOfArity ``Eq 3 && condition.getAppArgs[0]!.isConstOf ``Bool && condition.getAppArgs[2]!.isConstOf ``Bool.true then
        let evidence ← Lean.Elab.Term.exprToSyntax declaration.toExpr
        Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [Bool.not_eq_true] at ($evidence)))
        return
  throwError "no negative native boolean branch remains"

local macro "statement_inverse " equation:ident : tactic => `(tactic|
  repeat' first
    | (solve | statement_native_contradiction)
    | statement_causal_booleans
    | statement_causal_results
    | statement_execute_result
    | (solve | statement_causal_child)
    | (solve | statement_native_escape)
    | statement_inverse_result $equation
    | statement_inverse_reduce $equation
    | statement_split_escape $equation
    | statement_inverse_recorded)

private theorem statementInvocation_assign_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (p : Place) (e : Expr) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.assign p e org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.assign p e org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_assignOp_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (op : Goose.Core.BinOp) (p : Place) (e : Expr) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.assignOp op p e org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.assignOp op p e org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_rebind_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (x : Goose.Core.VarId) (e : Expr) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.rebind x e org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.rebind x e org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_expr_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (e : Expr) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.expr e org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.expr e org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_append_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (owner : Place) (src : View) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.append owner src org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.append owner src org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_popN_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (owner : Place) (count : Expr) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.popN owner count org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.popN owner count org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_resize_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (owner : Place) (size : Expr) (fill : Option Expr) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.resize owner size fill org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.resize owner size fill org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_clear_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (owner : Place) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.clear owner org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.clear owner org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_ifS_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (c : Expr) (thenB : Block) (elseB : Option Block) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.ifS c thenB elseB org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.ifS c thenB elseB org)) initial address carriers := by
  rw [execStmt.eq_def] at escaped
  dsimp only at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_while_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (c : Expr) (body : Block) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.while c body org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.while c body org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_forRange_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (x : Goose.Core.VarId) (lo : Expr) (hi : Expr) (body : Block) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.forRange x lo hi body org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.forRange x lo hi body org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_forEach_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (x : Goose.Core.VarId) (index : Option Goose.Core.VarId) (v : View) (byRef : Bool) (body : Block) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.forEach x index v byRef body org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.forEach x index v byRef body org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_receive_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (vars : List Goose.Core.VarId) (producer : Expr) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.receive vars producer org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.receive vars producer org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_appendValue_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (owner : Place) (producer : Expr) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.appendValue owner producer org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.appendValue owner producer org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_appendConstruct_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (owner : Place) (producer : Expr) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.appendConstruct owner producer org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.appendConstruct owner producer org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_brk_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.brk org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.brk org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_cont_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.cont org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.cont org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_assertS_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (e : Expr) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.assertS e org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.assertS e org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_abort_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (message : String) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.abort message org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.abort message org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementInvocation_exit_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (e : Expr) (org : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (Stmt.exit e org) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (Stmt.exit e org)) initial address carriers := by
  try simp only [execStmt] at escaped
  statement_inverse escaped
  all_goals (try subst_vars)
  all_goals statement_inverse escaped

private theorem statementWhile_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (condition : Expr) (body : Block) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execWhile fuel config environment condition body initial = .escape address carriers final) :
    StatementCausalChild config (.whileLoop fuel environment condition body) initial address carriers := by
  cases fuel with
  | zero => simp [execWhile, timeout, EvalM.stop] at escaped
  | succ fuel =>
      simp only [execWhile] at escaped
      statement_inverse escaped
      all_goals (try subst_vars)
      all_goals statement_inverse escaped

private theorem statementRange_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (ty : Goose.Core.IntTy) (first : Int) (last : Int) (body : Block) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execRange fuel config environment localVar ty first last body initial = .escape address carriers final) :
    StatementCausalChild config (.rangeLoop fuel environment localVar ty first last body) initial address carriers := by
  cases fuel with
  | zero => simp [execRange, timeout, EvalM.stop] at escaped
  | succ fuel =>
      simp only [execRange] at escaped
      statement_inverse escaped
      all_goals (try subst_vars)
      all_goals statement_inverse escaped

private theorem statementEach_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block) (view : RuntimeView) (current : Nat) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execEach fuel config environment localVar index byRef body view current initial = .escape address carriers final) :
    StatementCausalChild config (.eachLoop fuel environment localVar index byRef body view current) initial address carriers := by
  cases fuel with
  | zero => simp [execEach, timeout, EvalM.stop] at escaped
  | succ fuel =>
      simp only [execEach] at escaped
      statement_inverse escaped
      all_goals (try subst_vars)
      all_goals statement_inverse escaped

private theorem statementPush_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : Goose.Construct.pushValue fuel config environment owner expression origin initial = .escape address carriers final) :
    StatementCausalChild config (.push fuel environment owner expression origin) initial address carriers := by
  cases fuel with
  | zero => simp [Goose.Construct.pushValue, timeout, EvalM.stop] at escaped
  | succ fuel =>
      simp only [Goose.Construct.pushValue] at escaped
      statement_inverse escaped
      all_goals (try subst_vars)
      all_goals statement_inverse escaped

private theorem statementGlobals_escape_inv (fuel : Nat) (config : EvalConfig)
    (globals : List Goose.Core.GlobalId) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : initGlobals fuel config globals initial = .escape address carriers final) :
    StatementCausalChild config (.globals fuel globals) initial address carriers := by
  cases globals with
  | nil => simp [initGlobals, pure] at escaped
  | cons global globals =>
      rw [statementGlobal_next_action] at escaped
      statement_inverse escaped
      all_goals (try subst_vars)
      all_goals statement_inverse escaped

theorem statementInvocation_escape_inv (config : EvalConfig)
    {α : Type} (parent : ExitInvocation α) (source : StatementInvocationSource parent)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : parent.action config initial = .escape address carriers final) :
    StatementCausalChild config parent initial address carriers := by
  cases parent
  all_goals simp only [StatementInvocationSource] at source
  all_goals try (cases source)
  case statement fuel environment statement =>
    cases fuel with
    | zero => simp [ExitInvocation.action, execStmt, timeout, EvalM.stop] at escaped
    | succ fuel =>
        simp only [ExitInvocation.action] at escaped
        cases statement with
        | letS x e org =>
            exact statementInvocation_letS_escape_inv fuel config environment x e org initial final address carriers escaped
        | assign p e org =>
            exact statementInvocation_assign_escape_inv fuel config environment p e org initial final address carriers escaped
        | assignOp op p e org =>
            exact statementInvocation_assignOp_escape_inv fuel config environment op p e org initial final address carriers escaped
        | rebind x e org =>
            exact statementInvocation_rebind_escape_inv fuel config environment x e org initial final address carriers escaped
        | expr e org =>
            exact statementInvocation_expr_escape_inv fuel config environment e org initial final address carriers escaped
        | append owner src org =>
            exact statementInvocation_append_escape_inv fuel config environment owner src org initial final address carriers escaped
        | popN owner count org =>
            exact statementInvocation_popN_escape_inv fuel config environment owner count org initial final address carriers escaped
        | resize owner size fill org =>
            exact statementInvocation_resize_escape_inv fuel config environment owner size fill org initial final address carriers escaped
        | clear owner org =>
            exact statementInvocation_clear_escape_inv fuel config environment owner org initial final address carriers escaped
        | assignWhole owner replacement org =>
            exact statementAssignWhole_escape_inv fuel config environment owner replacement org initial final address carriers escaped
        | ifS c thenB elseB org =>
            exact statementInvocation_ifS_escape_inv fuel config environment c thenB elseB org initial final address carriers escaped
        | «while» c body org =>
            exact statementInvocation_while_escape_inv fuel config environment c body org initial final address carriers escaped
        | forRange x lo hi body org =>
            exact statementInvocation_forRange_escape_inv fuel config environment x lo hi body org initial final address carriers escaped
        | forEach x index v byRef body org =>
            exact statementInvocation_forEach_escape_inv fuel config environment x index v byRef body org initial final address carriers escaped
        | receive vars producer org =>
            exact statementInvocation_receive_escape_inv fuel config environment vars producer org initial final address carriers escaped
        | appendValue owner producer org =>
            exact statementInvocation_appendValue_escape_inv fuel config environment owner producer org initial final address carriers escaped
        | appendConstruct owner producer org =>
            exact statementInvocation_appendConstruct_escape_inv fuel config environment owner producer org initial final address carriers escaped
        | retValues operands org =>
            cases source
        | retForward call org =>
            cases source
        | returnFrom target operands org =>
            cases source
        | returnFromForward target call org =>
            cases source
        | breakValue value org =>
            cases source
        | ret e org =>
            cases source
        | brk org =>
            exact statementInvocation_brk_escape_inv fuel config environment org initial final address carriers escaped
        | cont org =>
            exact statementInvocation_cont_escape_inv fuel config environment org initial final address carriers escaped
        | print args org =>
            exact statement_print_escape_inv fuel config environment args org initial final address carriers escaped
        | assertS e org =>
            exact statementInvocation_assertS_escape_inv fuel config environment e org initial final address carriers escaped
        | abort message org =>
            exact statementInvocation_abort_escape_inv fuel config environment message org initial final address carriers escaped
        | exit e org =>
            exact statementInvocation_exit_escape_inv fuel config environment e org initial final address carriers escaped
  case whileLoop fuel environment condition body =>
    exact statementWhile_escape_inv fuel config environment condition body initial final address carriers escaped
  case rangeLoop fuel environment localVar ty first last body =>
    exact statementRange_escape_inv fuel config environment localVar ty first last body initial final address carriers escaped
  case eachLoop fuel environment localVar index byRef body view current =>
    exact statementEach_escape_inv fuel config environment localVar index byRef body view current initial final address carriers escaped
  case loop fuel environment pre body =>
    exact statementLoopBlock_escape_inv fuel config environment pre body initial final address carriers escaped
  case push fuel environment owner expression origin =>
    exact statementPush_escape_inv fuel config environment owner expression origin initial final address carriers escaped
  case globals fuel globals =>
    exact statementGlobals_escape_inv fuel config globals initial final address carriers escaped

end Goose.Proofs.ExitExecution
