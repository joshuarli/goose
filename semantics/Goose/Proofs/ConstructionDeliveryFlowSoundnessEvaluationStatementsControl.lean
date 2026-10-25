import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsSimple

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationControl_statement_if_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (condition : Expr) (yes : Block) (no : Option Block) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.ifS condition yes no origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.ifS condition yes no origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.ifS condition yes no origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    cases no with
    | none =>
      have budgets : expressionQueryBudget condition + blockQueryBudget yes + 1 + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act
        (continueFlows (expressionFlows staticFuel condition) (blockFlows staticFuel yes ++ [normalFlow])) resultControlFlow _
      simp only [execStmt]
      apply controlFlow_bind
      · exact previous.value environment condition staticFuel (by omega)
      · intro value
        apply controlFlow_prefix
        · evaluation_values_normal
        · intro selected
          apply controlFlow_conditional
          · exact controlFlow_mono _ _ _ _ (fun _ present => List.mem_append_left _ present)
              (previous.block environment [] [] yes staticFuel (by omega))
          · exact controlFlow_pure _ _ _ (List.mem_append_right _ (List.mem_singleton_self _))
    | some other =>
      have budgets : expressionQueryBudget condition + blockQueryBudget yes + blockQueryBudget other + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act
        (continueFlows (expressionFlows staticFuel condition) (blockFlows staticFuel yes ++ blockFlows staticFuel other)) resultControlFlow _
      simp only [execStmt]
      apply controlFlow_bind
      · exact previous.value environment condition staticFuel (by omega)
      · intro value
        apply controlFlow_prefix
        · evaluation_values_normal
        · intro selected
          apply controlFlow_conditional
          · exact controlFlow_mono _ _ _ _ (fun _ present => List.mem_append_left _ present)
              (previous.block environment [] [] yes staticFuel (by omega))
          · exact controlFlow_mono _ _ _ _ (fun _ present => List.mem_append_right _ present)
              (previous.block environment [] [] other staticFuel (by omega))

theorem evaluationControl_statement_appendConstruct_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.appendConstruct owner expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.appendConstruct owner expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.appendConstruct owner expression origin)) := by
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
      · intro value
        cases value with
        | stored stored =>
          apply controlFlow_suffix
          · apply controlFlow_withOwnerExtension
            · evaluation_values_normal
            · intro destination
              apply controlFlow_suffix
              · exact previous.build environment destination expression staticFuel (by omega)
              · intro ignored
                evaluation_values_normal
          · intro ignored
            evaluation_statements_normal
        | int ty value | bool value | unit | ref location | slice location start count | fixed values | record id fields =>
          exact controlFlow_stop _ _ _

#print axioms evaluationControl_statement_if_succ
#print axioms evaluationControl_statement_appendConstruct_succ

end Goose.Proofs.ConstructionDelivery
