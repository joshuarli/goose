import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationValuesHelpers

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationControl_bound_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (count : Nat) (defaultValue : Int) (operand : Bound) (staticFuel : Nat)
    (enough : boundQueryBudget operand ≤ staticFuel) :
    ControlFlowAction environment.act (boundFlows staticFuel operand) (fun _ => normalFlow)
      (evalBound (fuel + 1) config environment count defaultValue operand) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (boundQueryBudget_positive operand) enough)
  | succ staticFuel =>
    cases operand with
    | omitted => simp only [evalBound]; evaluation_values_normal
    | expr expression =>
      have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act (expressionFlows staticFuel expression) (fun _ => normalFlow) _
      simp only [evalBound]
      apply controlFlow_suffix
      · exact previous.value environment expression staticFuel (by omega)
      · intro value; evaluation_values_normal
    | fromEnd expression =>
      have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act (expressionFlows staticFuel expression) (fun _ => normalFlow) _
      simp only [evalBound]
      apply controlFlow_suffix
      · exact previous.value environment expression staticFuel (by omega)
      · intro value; evaluation_values_normal

theorem evaluationControl_place_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (operand : Place) (staticFuel : Nat) (enough : placeQueryBudget operand ≤ staticFuel) :
    ControlFlowAction environment.act (placeFlows staticFuel operand) (fun _ => normalFlow)
      (evalPlace (fuel + 1) config environment operand) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (placeQueryBudget_positive operand) enough)
  | succ staticFuel =>
    cases operand with
    | var localVar => simp only [evalPlace]; evaluation_values_normal
    | global global => simp only [evalPlace]; evaluation_values_normal
    | deref expression =>
      have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act (expressionFlows staticFuel expression) (fun _ => normalFlow) _
      simp only [evalPlace]
      apply controlFlow_suffix
      · exact previous.value environment expression staticFuel (by omega)
      · intro value; evaluation_values_normal
    | field owner index =>
      have budgets : placeQueryBudget owner + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act (placeFlows staticFuel owner) (fun _ => normalFlow) _
      simp only [evalPlace]
      apply controlFlow_suffix
      · exact previous.place environment owner staticFuel (by omega)
      · intro location; evaluation_values_normal
    | elem view expression origin =>
      have budgets : viewQueryBudget view + expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act
        (continueFlows (viewFlows staticFuel view) (expressionFlows staticFuel expression)) (fun _ => normalFlow) _
      simp only [evalPlace]
      apply controlFlow_bind
      · exact previous.view environment view staticFuel (by omega)
      · intro runtimeView
        apply controlFlow_suffix
        · exact previous.value environment expression staticFuel (by omega)
        · intro value; evaluation_values_normal

theorem evaluationControl_view_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (operand : View) (staticFuel : Nat) (enough : viewQueryBudget operand ≤ staticFuel) :
    ControlFlowAction environment.act (viewFlows staticFuel operand) (fun _ => normalFlow)
      (evalView (fuel + 1) config environment operand) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (viewQueryBudget_positive operand) enough)
  | succ staticFuel =>
    cases operand with
    | of place =>
      have budgets : placeQueryBudget place + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act (placeFlows staticFuel place) (fun _ => normalFlow) _
      simp only [evalView]
      apply controlFlow_suffix
      · exact previous.place environment place staticFuel (by omega)
      · intro location; evaluation_values_normal
    | val expression =>
      have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act (expressionFlows staticFuel expression) (fun _ => normalFlow) _
      simp only [evalView]
      apply controlFlow_suffix
      · exact previous.value environment expression staticFuel (by omega)
      · intro value; evaluation_values_normal

theorem evaluationControl_printArgument_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (argument : PrintArg) (staticFuel : Nat) (enough : printArgumentQueryBudget argument ≤ staticFuel) :
    ControlFlowAction environment.act (printArgumentFlows staticFuel argument) (fun _ => normalFlow)
      (evalPrintArg (fuel + 1) config environment argument) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (printArgumentQueryBudget_positive argument) enough)
  | succ staticFuel =>
    cases argument with
    | text text => simp only [evalPrintArg]; evaluation_values_normal
    | expr expression =>
      have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act (expressionFlows staticFuel expression) (fun _ => normalFlow) _
      simp only [evalPrintArg]
      apply controlFlow_suffix
      · exact previous.value environment expression staticFuel (by omega)
      · intro value; evaluation_values_normal
    | view view =>
      have budgets : viewQueryBudget view + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act (viewFlows staticFuel view) (fun _ => normalFlow) _
      simp only [evalPrintArg]
      apply controlFlow_suffix
      · exact previous.view environment view staticFuel (by omega)
      · intro value; evaluation_values_normal

#print axioms evaluationControl_bound_succ
#print axioms evaluationControl_place_succ
#print axioms evaluationControl_view_succ
#print axioms evaluationControl_printArgument_succ

end Goose.Proofs.ConstructionDelivery
