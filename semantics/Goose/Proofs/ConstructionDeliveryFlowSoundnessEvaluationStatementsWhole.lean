import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsResize

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationControl_statement_assignWhole_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.assignWhole owner expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.assignWhole owner expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.assignWhole owner expression origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : placeQueryBudget owner + expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act
      (continueFlows (placeFlows staticFuel owner) (expressionFlows staticFuel expression)) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_bind
    · exact previous.place environment owner staticFuel (by omega)
    · intro location
      apply controlFlow_prefix
      · evaluation_values_normal
      · intro cleared
        apply controlFlow_prefix
        · evaluation_values_normal
        · intro value
          cases value with
          | stored stored =>
            apply controlFlow_materializeProducer_then
            · exact previous.value environment expression staticFuel (by omega)
            · apply controlFlow_suffix
              · apply controlFlow_withOwnerExtension
                · evaluation_values_normal
                · intro destination
                  apply controlFlow_suffix
                  · exact previous.build environment destination expression staticFuel (by omega)
                  · intro ignored
                    evaluation_values_normal
              · intro ignored
                evaluation_statements_normal
            · intro values
              apply controlFlow_prefix
              · apply controlFlow_withOwnerExtension
                · evaluation_values_normal
                · intro destination
                  evaluation_values_normal
              · intro ignored
                evaluation_statements_normal
          | int ty value | bool value | unit | ref location | slice location start count | fixed values | record id fields =>
            exact controlFlow_stop _ _ _

#print axioms evaluationControl_statement_assignWhole_succ

end Goose.Proofs.ConstructionDelivery
