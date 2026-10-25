import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsReceive

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct
open Goose.Core (VarId OriginId)

private theorem letPure_bind (value : α) (next : α → EvalM β) :
    ((pure value : EvalM α) >>= next) = next value := rfl

local elab "let_step" previous:ident environment:ident expression:ident staticFuel:ident : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  if target.isForall then
    Lean.Elab.Tactic.evalTactic (← `(tactic| intro))
    return
  let args := target.getAppArgs
  let some action := args[args.size - 1]? | throwError "expected action"
  if action.isLet then
    Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))
    return
  let name := action.getAppFn.constName?
  if name == some ``Bind.bind then
    let args := action.getAppArgs
    let some head := args[args.size - 2]? | throwError "expected head"
    let headName := head.getAppFn.constName?
    if headName == some ``fault || headName == some ``EvalM.stop then
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact controlFlow_stop _ _ _))
    else if headName == some ``Pure.pure then
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [letPure_bind]))
    else if headName == some ``materializeProducer then
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply controlFlow_materializeProducer_then))
    else if headName == some ``evalValue || headName == some ``buildExpr then
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply controlFlow_suffix))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply controlFlow_prefix))
  else if name == some ``ite then
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply controlFlow_conditional))
  else if name == some ``evalValue then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($previous).value $environment $expression $staticFuel (by omega)))
  else if name == some ``buildExpr then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($previous).build $environment _ $expression $staticFuel (by omega)))
  else if name == some ``materializedDestination then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact controlFlow_normal _ (breakFrame_materializedDestination _ _ _ _ _ _ _) (neverJumps_materializedDestination _ _ _ _ _ _ _)))
  else if name == some ``Pure.pure then
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply controlFlow_pure; exact List.mem_singleton_self _))
  else if name == some ``fault || name == some ``EvalM.stop then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact controlFlow_stop _ _ _))
  else if name == some ``EvalM.get || (name.map (·.getPrefix) == some `Goose.Construct) then
    let some (.str _ suffix) := name | throwError "expected primitive name"
    let frame := Lean.mkIdent (`Goose.Proofs.ConstructionDelivery ++ .str .anonymous ("breakFrame_" ++ suffix))
    let noJump := Lean.mkIdent (`Goose.Proofs.ConstructionDelivery ++ .str .anonymous ("neverJumps_" ++ (if suffix == "liftConstruction" then "lift" else suffix)))
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact controlFlow_normal _ (by apply $frame) (by apply $noJump)))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| split))

theorem evaluationControl_statement_let_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (localVar : VarId) (expression : Expr) (origin : OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.letS localVar expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.letS localVar expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.letS localVar expression origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (expressionFlows staticFuel expression) resultControlFlow _
    simp only [execStmt]
    repeat' first
      | contradiction
      | let_step previous environment expression staticFuel

#print axioms evaluationControl_statement_let_succ

end Goose.Proofs.ConstructionDelivery
