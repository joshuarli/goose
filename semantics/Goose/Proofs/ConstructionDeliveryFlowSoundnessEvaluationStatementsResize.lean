import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsBreak

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationControl_statement_resize_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (fill : Option Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.resize owner expression fill origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.resize owner expression fill origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.resize owner expression fill origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    cases fill with
    | none =>
      have budgets : placeQueryBudget owner + expressionQueryBudget expression + 1 + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act
        (continueFlows (placeFlows staticFuel owner) (continueFlows (expressionFlows staticFuel expression) [normalFlow])) resultControlFlow _
      rw [continueFlows_normal_right]
      simp only [execStmt]
      apply controlFlow_bind
      · exact previous.place environment owner staticFuel (by omega)
      · intro location
        apply controlFlow_suffix
        · exact previous.value environment expression staticFuel (by omega)
        · intro value
          evaluation_statements_normal
    | some fill =>
      have budgets : placeQueryBudget owner + expressionQueryBudget expression + expressionQueryBudget fill + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act
        (continueFlows (placeFlows staticFuel owner) (continueFlows (expressionFlows staticFuel expression) (expressionFlows staticFuel fill))) resultControlFlow _
      simp only [execStmt]
      apply controlFlow_bind
      · exact previous.place environment owner staticFuel (by omega)
      · intro location
        apply controlFlow_bind
        · exact previous.value environment expression staticFuel (by omega)
        · intro value
          apply controlFlow_prefix
          · evaluation_values_normal
          · rintro ⟨integer, size⟩
            apply controlFlow_suffix
            · exact previous.value environment fill staticFuel (by omega)
            · intro value
              evaluation_statements_normal

#print axioms evaluationControl_statement_resize_succ

end Goose.Proofs.ConstructionDelivery
