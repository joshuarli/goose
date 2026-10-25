import Goose.Proofs.ExitExecutionPathContext
import Goose.Proofs.ExitExecutionInvocationProducersEscapeSupport

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem operandsInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalOperands fuel config environment channels operands initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitCallSite config (.operands fuel environment channels operands) initial child prepared ∧
      child.action config prepared = .escape address carriers final := by
  cases fuel with
  | zero => simp only [evalOperands, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
    cases channels with
    | nil => cases operands <;> simp only [evalOperands, pure, fault, EvalM.stop] at escaped <;> cases escaped
    | cons channel channels =>
      cases operands with
      | nil => simp only [evalOperands, fault, EvalM.stop] at escaped; cases escaped
      | cons operand operands =>
        simp only [evalOperands, bind] at escaped
        cases produced : evalProduce fuel config environment [channel] operand initial with
        | stop reason state | jump target kind state =>
          simp only [produced] at escaped
          cases escaped
        | escape target payload state =>
          simp only [produced] at escaped
          cases escaped
          exact ⟨List Carrier, .produce fuel environment [channel] operand, initial,
            .operandsHead fuel environment channel channels operand operands initial, produced⟩
        | ok producedCarriers producedState =>
          simp only [produced] at escaped
          cases selected : singleCarrier producedCarriers producedState with
          | stop reason state | jump target kind state =>
            simp only [selected] at escaped
            cases escaped
          | escape target payload state =>
            exact False.elim (producerNeverEscapes_singleCarrier producedCarriers producedState target payload state selected)
          | ok carrier middle =>
            simp only [selected] at escaped
            cases tail : evalOperands fuel config environment channels operands middle with
            | stop reason state | jump target kind state =>
              simp only [tail] at escaped
              cases escaped
            | ok values state =>
              simp only [tail, pure] at escaped
              cases escaped
            | escape target payload state =>
              simp only [tail] at escaped
              cases escaped
              exact ⟨List Carrier, .operands fuel environment channels operands, middle,
                .operandsTail fuel environment channel channels operand operands initial producedState middle
                  producedCarriers carrier produced selected, tail⟩

theorem statementsInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (statements : List Stmt) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : execStmts fuel config environment statements initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitCallSite config (.statements fuel environment statements) initial child prepared ∧
      child.action config prepared = .escape address carriers final := by
  cases fuel with
  | zero => simp only [execStmts, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
    cases statements with
    | nil => simp only [execStmts, pure] at escaped; cases escaped
    | cons statement statements =>
      simp only [execStmts, bind] at escaped
      cases evaluated : execStmt fuel config environment statement initial with
      | stop reason state | jump target kind state =>
        simp only [evaluated] at escaped
        cases escaped
      | escape target payload state =>
        simp only [evaluated] at escaped
        cases escaped
        exact ⟨Flow, .statement fuel environment statement, initial,
          .statementsHead fuel environment statement statements initial, evaluated⟩
      | ok flow middle =>
        simp only [evaluated] at escaped
        cases flow with
        | normal value =>
          exact ⟨Flow, .statements fuel environment statements, middle,
            .statementsTail fuel environment statement statements initial middle value evaluated, escaped⟩
        | breaking value | continuing => cases escaped

end Goose.Proofs.ExitExecution
