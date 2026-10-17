import Goose.Proofs.ConstructionDeliveryFlowSoundnessBudgets
import Goose.Proofs.ConstructionDeliveryFlowSoundnessComposition
import Goose.Construct.Eval

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

abbrev escapingControlFlow (flow : StaticFlow) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left) (escapesFlow_transition flow)

def loopControlFlows (staticFuel : Nat) (body : Block) : List StaticFlow :=
  normalFlow :: (blockFlows staticFuel body).filter escapingControlFlow

structure EvaluationControlFlows (fuel : Nat) (config : EvalConfig) : Prop where
  value : ∀ environment expression staticFuel, expressionQueryBudget expression ≤ staticFuel →
    ControlFlowAction environment.act (expressionFlows staticFuel expression) (fun _ => normalFlow)
      (evalValue fuel config environment expression)
  bound : ∀ environment count defaultValue operand staticFuel, boundQueryBudget operand ≤ staticFuel →
    ControlFlowAction environment.act (boundFlows staticFuel operand) (fun _ => normalFlow)
      (evalBound fuel config environment count defaultValue operand)
  place : ∀ environment operand staticFuel, placeQueryBudget operand ≤ staticFuel →
    ControlFlowAction environment.act (placeFlows staticFuel operand) (fun _ => normalFlow)
      (evalPlace fuel config environment operand)
  view : ∀ environment operand staticFuel, viewQueryBudget operand ≤ staticFuel →
    ControlFlowAction environment.act (viewFlows staticFuel operand) (fun _ => normalFlow)
      (evalView fuel config environment operand)
  produce : ∀ environment channels operand staticFuel, expressionQueryBudget operand ≤ staticFuel →
    ControlFlowAction environment.act (expressionFlows staticFuel operand) (fun _ => normalFlow)
      (evalProduce fuel config environment channels operand)
  operands : ∀ environment channels expressions staticFuel, expressionListQueryBudget expressions ≤ staticFuel →
    ControlFlowAction environment.act (expressionsFlows staticFuel expressions) (fun _ => normalFlow)
      (evalOperands fuel config environment channels expressions)
  build : ∀ environment destination expression staticFuel, expressionQueryBudget expression ≤ staticFuel →
    ControlFlowAction environment.act (expressionFlows staticFuel expression) (fun _ => normalFlow)
      (buildExpr fuel config environment destination expression)
  element : ∀ environment destination element expression staticFuel, expressionQueryBudget expression ≤ staticFuel →
    ControlFlowAction environment.act (expressionFlows staticFuel expression) (fun _ => normalFlow)
      (buildElement fuel config environment destination element expression)
  arguments : ∀ environment vars params args staticFuel, argumentsQueryBudget args ≤ staticFuel →
    ControlFlowAction environment.act (argumentsFlows staticFuel args) (fun _ => normalFlow)
      (evalArguments fuel config environment vars params args)
  call : ∀ environment context args channels origin staticFuel, argumentsQueryBudget args ≤ staticFuel →
    ControlFlowAction environment.act (argumentsFlows staticFuel args) (fun _ => normalFlow)
      (invokeCall fuel config environment context args channels origin)
  resultBlock : ∀ environment channels body staticFuel, blockQueryBudget body ≤ staticFuel →
    ControlFlowAction environment.act (blockFlows staticFuel body) (fun result => resultControlFlow result.1)
      (execResultBlock fuel config environment channels body)
  resultBlockWith : ∀ environment pre channels body staticFuel, blockQueryBudget body ≤ staticFuel →
    ControlFlowAction environment.act (blockFlows staticFuel body) (fun result => resultControlFlow result.1)
      (execResultBlockWith fuel config environment pre channels body)
  block : ∀ environment pre channels body staticFuel, blockQueryBudget body ≤ staticFuel →
    ControlFlowAction environment.act (blockFlows staticFuel body) resultControlFlow
      (execBlock fuel config environment pre channels body)
  statements : ∀ environment statements staticFuel, statementsQueryBudget statements ≤ staticFuel →
    ControlFlowAction environment.act (statementsFlows staticFuel statements) resultControlFlow
      (execStmts fuel config environment statements)
  statement : ∀ environment statement staticFuel, statementQueryBudget statement ≤ staticFuel →
    ControlFlowAction environment.act (statementFlows staticFuel statement) resultControlFlow
      (execStmt fuel config environment statement)
  printArgument : ∀ environment argument staticFuel, printArgumentQueryBudget argument ≤ staticFuel →
    ControlFlowAction environment.act (printArgumentFlows staticFuel argument) (fun _ => normalFlow)
      (evalPrintArg fuel config environment argument)
  whileLoop : ∀ environment condition body staticFuel, statementQueryBudget (.while condition body 0) ≤ staticFuel →
    ControlFlowAction environment.act (statementFlows staticFuel (.while condition body 0)) resultControlFlow
      (execWhile fuel config environment condition body)
  rangeLoop : ∀ environment var ty first last body staticFuel, blockQueryBudget body ≤ staticFuel →
    ControlFlowAction environment.act (loopControlFlows staticFuel body) resultControlFlow
      (execRange fuel config environment var ty first last body)
  eachLoop : ∀ environment var index byRef body view current staticFuel, blockQueryBudget body ≤ staticFuel →
    ControlFlowAction environment.act (loopControlFlows staticFuel body) resultControlFlow
      (execEach fuel config environment var index byRef body view current)
  loop : ∀ environment pre body staticFuel, blockQueryBudget body ≤ staticFuel →
    ControlFlowAction environment.act (blockFlows staticFuel body) resultControlFlow
      (loopBody fuel config environment pre body)
  loopIteration : ∀ environment pre body staticFuel, blockQueryBudget body ≤ staticFuel →
    ControlFlowAction environment.act (loopControlFlows staticFuel body) (fun _ => normalFlow)
      (loopBody fuel config environment pre body)
  push : ∀ environment owner expression origin staticFuel, expressionQueryBudget (.push owner expression origin) ≤ staticFuel →
    ControlFlowAction environment.act (expressionFlows staticFuel (.push owner expression origin)) (fun _ => normalFlow)
      (pushValue fuel config environment owner expression (origin.getD 0))

theorem evaluationControlFlows_zero (config : EvalConfig) : EvaluationControlFlows 0 config := by
  constructor <;> intros
  all_goals simp only [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
    buildExpr, buildElement, evalArguments, invokeCall, execResultBlock, execResultBlockWith,
    execBlock, execStmts, execStmt, evalPrintArg, execWhile, execRange, execEach, loopBody, pushValue]
  all_goals exact controlFlow_stop _ _ _

#print axioms evaluationControlFlows_zero

end Goose.Proofs.ConstructionDelivery
