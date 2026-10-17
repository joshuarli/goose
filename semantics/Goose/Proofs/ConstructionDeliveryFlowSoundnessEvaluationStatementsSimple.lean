import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsHelpers

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationControl_statement_expr_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : statementQueryBudget (.expr expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.expr expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.expr expression origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (expressionFlows staticFuel expression) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_suffix
    · exact previous.value environment expression staticFuel (by omega)
    · intro value
      evaluation_statements_normal

theorem evaluationControl_statement_rebind_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : statementQueryBudget (.rebind localVar expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.rebind localVar expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.rebind localVar expression origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (expressionFlows staticFuel expression) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_suffix
    · exact previous.value environment expression staticFuel (by omega)
    · intro value
      evaluation_statements_normal

theorem evaluationControl_statement_assert_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat) (enough : statementQueryBudget (.assertS expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.assertS expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.assertS expression origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (expressionFlows staticFuel expression) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_suffix
    · exact previous.value environment expression staticFuel (by omega)
    · intro value
      evaluation_statements_normal

theorem evaluationControl_statement_clear_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (owner : Place) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.clear owner origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.clear owner origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.clear owner origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : placeQueryBudget owner + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (placeFlows staticFuel owner) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_suffix
    · exact previous.place environment owner staticFuel (by omega)
    · intro location
      evaluation_statements_normal

theorem evaluationControl_statement_assign_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.assign owner expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.assign owner expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.assign owner expression origin)) := by
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
      apply controlFlow_suffix
      · exact previous.value environment expression staticFuel (by omega)
      · intro value
        evaluation_statements_normal

theorem evaluationControl_statement_popN_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.popN owner expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.popN owner expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.popN owner expression origin)) := by
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
      apply controlFlow_suffix
      · exact previous.value environment expression staticFuel (by omega)
      · intro value
        evaluation_statements_normal

theorem evaluationControl_statement_appendValue_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.appendValue owner expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.appendValue owner expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.appendValue owner expression origin)) := by
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
      apply controlFlow_suffix
      · exact previous.value environment expression staticFuel (by omega)
      · intro value
        evaluation_statements_normal

theorem evaluationControl_statement_append_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (owner : Place) (view : View) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.append owner view origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.append owner view origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.append owner view origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : placeQueryBudget owner + viewQueryBudget view + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act
      (continueFlows (placeFlows staticFuel owner) (viewFlows staticFuel view)) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_bind
    · exact previous.place environment owner staticFuel (by omega)
    · intro location
      apply controlFlow_suffix
      · exact previous.view environment view staticFuel (by omega)
      · intro value
        evaluation_statements_normal

theorem evaluationControl_statement_assignOp_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.BinOp) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.assignOp operation owner expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.assignOp operation owner expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.assignOp operation owner expression origin)) := by
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
      · intro old
        apply controlFlow_prefix
        · evaluation_values_normal
        · rintro ⟨integer, first⟩
          apply controlFlow_suffix
          · exact previous.value environment expression staticFuel (by omega)
          · intro value
            evaluation_statements_normal

theorem evaluationControl_statement_abort_succ (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (message : String) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.abort message origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.abort message origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.abort message origin)) := by
  simp only [execStmt]
  exact controlFlow_stop _ _ _

theorem evaluationControl_statement_break_succ (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.brk origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.brk origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.brk origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    simp only [execStmt]
    exact controlFlow_jump .loop (.breakValue []) True.intro

theorem evaluationControl_statement_continue_succ (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.cont origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.cont origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.cont origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    simp only [execStmt]
    exact controlFlow_jump .loop .continueLoop rfl

theorem evaluationControl_statement_exit_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.exit expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.exit expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.exit expression origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (continueFlows (expressionFlows staticFuel expression) [escapingFlow]) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_bind
    · exact previous.value environment expression staticFuel (by omega)
    · intro value
      apply controlFlow_prefix
      · evaluation_values_normal
      · rintro ⟨integer, code⟩
        exact controlFlow_stop _ _ _

theorem evaluationControl_statement_print_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (arguments : List PrintArg) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.print arguments origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.print arguments origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.print arguments origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : printArgumentsQueryBudget arguments + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (printArgumentsFlows staticFuel arguments) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_suffix
    · exact evaluationControl_printArguments_map fuel config previous environment arguments staticFuel (by omega)
    · intro bytes
      evaluation_statements_normal

theorem evaluationControl_statement_while_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (condition : Expr) (body : Block) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.while condition body origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.while condition body origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.while condition body origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    simp only [execStmt]
    exact previous.whileLoop environment condition body (staticFuel + 1) enough

theorem evaluationControl_statement_range_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (first last : Expr) (body : Block) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.forRange localVar first last body origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.forRange localVar first last body origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.forRange localVar first last body origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget first + expressionQueryBudget last + blockQueryBudget body + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act
      (continueFlows (expressionFlows staticFuel first) (continueFlows (expressionFlows staticFuel last) (loopControlFlows staticFuel body))) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_bind
    · exact previous.value environment first staticFuel (by omega)
    · intro firstValue
      apply controlFlow_prefix
      · evaluation_values_normal
      · rintro ⟨integer, first⟩
        apply controlFlow_bind
        · exact previous.value environment last staticFuel (by omega)
        · intro lastValue
          apply controlFlow_prefix
          · evaluation_values_normal
          · rintro ⟨otherInteger, last⟩
            apply controlFlow_prefix
            · evaluation_values_normal
            · intro ignored
              exact previous.rangeLoop environment localVar integer first last body staticFuel (by omega)

theorem evaluationControl_statement_each_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (view : View) (byRef : Bool)
    (body : Block) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.forEach localVar index view byRef body origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.forEach localVar index view byRef body origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.forEach localVar index view byRef body origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : viewQueryBudget view + blockQueryBudget body + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act
      (continueFlows (viewFlows staticFuel view) (loopControlFlows staticFuel body)) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_bind
    · exact previous.view environment view staticFuel (by omega)
    · intro sampled
      exact previous.eachLoop environment localVar index byRef body sampled 0 staticFuel (by omega)


#print axioms evaluationControl_statement_expr_succ
#print axioms evaluationControl_statement_rebind_succ
#print axioms evaluationControl_statement_assert_succ
#print axioms evaluationControl_statement_clear_succ
#print axioms evaluationControl_statement_assign_succ
#print axioms evaluationControl_statement_popN_succ
#print axioms evaluationControl_statement_appendValue_succ
#print axioms evaluationControl_statement_append_succ

#print axioms evaluationControl_statement_assignOp_succ
#print axioms evaluationControl_statement_abort_succ
#print axioms evaluationControl_statement_break_succ
#print axioms evaluationControl_statement_continue_succ
#print axioms evaluationControl_statement_exit_succ
#print axioms evaluationControl_statement_print_succ
#print axioms evaluationControl_statement_while_succ
#print axioms evaluationControl_statement_range_succ
#print axioms evaluationControl_statement_each_succ

end Goose.Proofs.ConstructionDelivery
