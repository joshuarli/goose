import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationValuesHelpers

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem controlFlow_constructLocal (allowed : List StaticFlow) (declarations : DeclarationEnv)
    (owner : Goose.Core.ActId) (ty : Ty) (origin : Goose.Core.OriginId) (expression : Expr)
    (construct : Goose.Core.DestinationId → EvalM Unit)
    (body : ∀ destination, ControlFlowAction activation allowed (fun _ => normalFlow) (construct destination)) :
    ControlFlowAction activation allowed (fun _ => normalFlow)
      (constructLocal declarations owner ty origin expression construct) := by
  unfold constructLocal
  apply controlFlow_prefix
  · evaluation_values_normal
  · intro destination
    apply controlFlow_suffix
    · exact body destination
    · intro ignored
      evaluation_values_normal

private theorem evaluationControl_values_loop (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (expressions : List Expr) (staticFuel : Nat) (enough : expressionListQueryBudget expressions ≤ staticFuel)
    (accumulator : List Value) :
    ControlFlowAction environment.act (expressionsFlows staticFuel expressions) (fun _ => normalFlow)
      (List.mapM.loop (evalValue fuel config environment) expressions accumulator) := by
  induction expressions generalizing staticFuel accumulator with
  | nil =>
      cases staticFuel with
      | zero => exact False.elim (Nat.not_le_of_gt (expressionListQueryBudget_positive []) enough)
      | succ staticFuel => exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
  | cons expression rest ih =>
      cases staticFuel with
      | zero => exact False.elim (Nat.not_le_of_gt (expressionListQueryBudget_positive _) enough)
      | succ staticFuel =>
        have budgets : expressionQueryBudget expression + expressionListQueryBudget rest + 1 ≤ staticFuel + 1 := enough
        have firstEnough : expressionQueryBudget expression ≤ staticFuel := by omega
        have restEnough : expressionListQueryBudget rest ≤ staticFuel := by omega
        change ControlFlowAction environment.act
          (continueFlows (expressionFlows staticFuel expression) (expressionsFlows staticFuel rest)) (fun _ => normalFlow)
          (do let value ← evalValue fuel config environment expression
              List.mapM.loop (evalValue fuel config environment) rest (value :: accumulator))
        apply controlFlow_bind
        · exact previous.value environment expression staticFuel firstEnough
        · intro value; exact ih staticFuel restEnough (value :: accumulator)

theorem evaluationControl_values_map (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (expressions : List Expr) (staticFuel : Nat) (enough : expressionListQueryBudget expressions ≤ staticFuel) :
    ControlFlowAction environment.act (expressionsFlows staticFuel expressions) (fun _ => normalFlow)
      (expressions.mapM (evalValue fuel config environment)) :=
  evaluationControl_values_loop fuel config previous environment expressions staticFuel enough []

private theorem evaluationControl_print_loop (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (arguments : List PrintArg) (staticFuel : Nat) (enough : printArgumentsQueryBudget arguments ≤ staticFuel)
    (accumulator : List ByteArray) :
    ControlFlowAction environment.act (printArgumentsFlows staticFuel arguments) (fun _ => normalFlow)
      (List.mapM.loop (evalPrintArg fuel config environment) arguments accumulator) := by
  induction arguments generalizing staticFuel accumulator with
  | nil =>
      cases staticFuel with
      | zero => change 1 ≤ 0 at enough; omega
      | succ staticFuel => exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
  | cons argument rest ih =>
      cases staticFuel with
      | zero =>
          have positive := printArgumentsQueryBudget_positive (argument :: rest)
          omega
      | succ staticFuel =>
        have budgets : printArgumentQueryBudget argument + printArgumentsQueryBudget rest + 1 ≤ staticFuel + 1 := enough
        have firstEnough : printArgumentQueryBudget argument ≤ staticFuel := by omega
        have restEnough : printArgumentsQueryBudget rest ≤ staticFuel := by omega
        change ControlFlowAction environment.act
          (continueFlows (printArgumentFlows staticFuel argument) (printArgumentsFlows staticFuel rest)) (fun _ => normalFlow)
          (do let value ← evalPrintArg fuel config environment argument
              List.mapM.loop (evalPrintArg fuel config environment) rest (value :: accumulator))
        apply controlFlow_bind
        · exact previous.printArgument environment argument staticFuel firstEnough
        · intro value; exact ih staticFuel restEnough (value :: accumulator)

theorem evaluationControl_printArguments_map (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (arguments : List PrintArg) (staticFuel : Nat) (enough : printArgumentsQueryBudget arguments ≤ staticFuel) :
    ControlFlowAction environment.act (printArgumentsFlows staticFuel arguments) (fun _ => normalFlow)
      (arguments.mapM (evalPrintArg fuel config environment)) :=
  evaluationControl_print_loop fuel config previous environment arguments staticFuel enough []

#print axioms controlFlow_constructLocal
#print axioms evaluationControl_values_map
#print axioms evaluationControl_printArguments_map

end Goose.Proofs.ConstructionDelivery
