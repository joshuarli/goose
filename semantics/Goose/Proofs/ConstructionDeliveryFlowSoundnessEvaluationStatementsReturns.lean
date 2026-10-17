import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsControl

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationControl_statement_retValues_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (operands : List Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.retValues operands origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.retValues operands origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.retValues operands origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionListQueryBudget operands + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (continueFlows (expressionsFlows staticFuel operands) [escapingFlow]) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_prefix
    · exact controlFlow_normal (enclosingActivation environment) (breakFrame_enclosingActivation environment) (neverJumps_enclosingActivation environment)
    · intro activation
      apply controlFlow_bind
      · apply controlFlow_withExitChannels
        intro channels
        exact previous.operands environment channels operands staticFuel (by omega)
      · intro carriers
        exact controlFlow_returned _ _ _ _

theorem evaluationControl_statement_retForward_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.retForward expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.retForward expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.retForward expression origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (continueFlows (expressionFlows staticFuel expression) [escapingFlow]) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_prefix
    · exact controlFlow_normal (enclosingActivation environment) (breakFrame_enclosingActivation environment) (neverJumps_enclosingActivation environment)
    · intro activation
      apply controlFlow_bind
      · apply controlFlow_withExitChannels
        intro channels
        exact previous.produce environment channels expression staticFuel (by omega)
      · intro carriers
        exact controlFlow_returned _ _ _ _

theorem evaluationControl_statement_returnFrom_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (target : Nat) (operands : List Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.returnFrom target operands origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.returnFrom target operands origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.returnFrom target operands origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionListQueryBudget operands + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (continueFlows (expressionsFlows staticFuel operands) [escapingFlow]) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_prefix
    · exact controlFlow_normal (targetActivation config target) (breakFrame_targetActivation config target) (neverJumps_targetActivation config target)
    · intro activation
      apply controlFlow_bind
      · apply controlFlow_withExitChannels
        intro channels
        exact previous.operands environment channels operands staticFuel (by omega)
      · intro carriers
        exact controlFlow_escaped _ _ _ _

theorem evaluationControl_statement_returnFromForward_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (target : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.returnFromForward target expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.returnFromForward target expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.returnFromForward target expression origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (continueFlows (expressionFlows staticFuel expression) [escapingFlow]) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_prefix
    · exact controlFlow_normal (targetActivation config target) (breakFrame_targetActivation config target) (neverJumps_targetActivation config target)
    · intro activation
      apply controlFlow_bind
      · apply controlFlow_withExitChannels
        intro channels
        exact previous.produce environment channels expression staticFuel (by omega)
      · intro carriers
        exact controlFlow_escaped _ _ _ _

theorem evaluationControl_statement_ret_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (expression : Option Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.ret expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.ret expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.ret expression origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    cases expression with
    | none =>
      change ControlFlowAction environment.act [escapingFlow] resultControlFlow _
      simp only [execStmt]
      apply controlFlow_prefix
      · exact controlFlow_normal _ (breakFrame_enclosingActivation environment) (neverJumps_enclosingActivation environment)
      · intro activation
        split
        · exact controlFlow_returned _ _ _ _
        · split
          · exact controlFlow_returned _ _ _ _
          · exact controlFlow_stop _ _ _
    | some expression =>
      have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
      change ControlFlowAction environment.act (continueFlows (expressionFlows staticFuel expression) [escapingFlow]) resultControlFlow _
      simp only [execStmt]
      apply controlFlow_prefix
      · exact controlFlow_normal _ (breakFrame_enclosingActivation environment) (neverJumps_enclosingActivation environment)
      · intro activation
        apply controlFlow_bind
        · apply controlFlow_withExitChannels
          intro channels
          exact previous.produce environment channels expression staticFuel (by omega)
        · intro carriers
          exact controlFlow_returned _ _ _ _

#print axioms evaluationControl_statement_ret_succ

#print axioms evaluationControl_statement_retValues_succ
#print axioms evaluationControl_statement_retForward_succ
#print axioms evaluationControl_statement_returnFrom_succ
#print axioms evaluationControl_statement_returnFromForward_succ

end Goose.Proofs.ConstructionDelivery
