import Goose.Proofs.ExitExecutionEvaluationBuild

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem freshLetPure_bind (value : α) (next : α → EvalM β) :
    ((pure value : EvalM α) >>= next) = next value := rfl

local elab "fresh_let_step" previous:ident environment:ident expression:ident : tactic => do
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
    if headName == some ``Pure.pure then
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [freshLetPure_bind]))
    else if headName == some ``fault || headName == some ``EvalM.stop then
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesFresh_stop _))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply preservesFresh_bind))
  else if name == some ``ite then
    Lean.Elab.Tactic.evalTactic (← `(tactic| fresh_conditional))
  else if name == some ``evalValue then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($previous).value $environment $expression))
  else if name == some ``buildExpr then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($previous).build $environment _ $expression))
  else if name == some ``materializeProducer then
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply preservesFresh_materializeProducer; exact ($previous).value $environment $expression))
  else if name == some ``Pure.pure then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesFresh_pure _))
  else if name == some ``fault || name == some ``EvalM.stop then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesFresh_stop _))
  else if name == some ``EvalM.get || (name.map (·.getPrefix) == some `Goose.Construct) then
    let some (.str _ suffix) := name | throwError "expected primitive name"
    let suffix := if suffix == "liftConstruction" then "lift" else suffix
    let freshName := `Goose.Proofs.ExitExecution ++ .str .anonymous ("preservesFresh_" ++ suffix)
    if (← Lean.getEnv).contains freshName then
      let fresh := Lean.mkIdent freshName
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply $fresh))
    else
      let query := Lean.mkIdent (`Goose.Proofs.ExitExecution ++ .str .anonymous ("stateQuery_" ++ suffix))
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact stateQuery_preservesFresh _ (by apply $query)))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| split))

theorem execStmt_letS_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.letS localVar expression origin)) := by
  simp only [execStmt]
  repeat' first
    | contradiction
    | fresh_let_step previous environment expression

#print axioms execStmt_letS_preservesFresh_succ

end Goose.Proofs.ExitExecution
