import Goose.Proofs.ExitExecutionPathSequences
import Goose.Proofs.ExitExecutionInvocationValues

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem ValueInvocationEdge.stop {config : EvalConfig}
    {parent : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (edge : ValueInvocationEdge config parent initial child prepared)
    (reason : Goose.Core.Stop) (final : ExecutionState)
    (stopped : child.action config prepared = .stop reason final) :
    parent.action config initial = .stop reason final := by
  cases edge
  all_goals simp only [ExitInvocation.action] at stopped ⊢
  all_goals simp_all [evalValue, evalBound, evalPlace, evalView, evalPrintArg, constructLocal,
    bind, List.mapM_append]

theorem operandsHead_escape_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channel : Channel) (channels : List Channel) (operand : Expr) (operands : List Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : evalProduce fuel config environment [channel] operand initial = .escape address carriers final) :
    evalOperands (fuel + 1) config environment (channel :: channels) (operand :: operands) initial =
      .escape address carriers final := by simp only [evalOperands, bind, escaped]

theorem operandsHead_stop_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channel : Channel) (channels : List Channel) (operand : Expr) (operands : List Expr)
    (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (stopped : evalProduce fuel config environment [channel] operand initial = .stop reason final) :
    evalOperands (fuel + 1) config environment (channel :: channels) (operand :: operands) initial =
      .stop reason final := by simp only [evalOperands, bind, stopped]

theorem operandsTail_escape_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channel : Channel) (channels : List Channel) (operand : Expr) (operands : List Expr)
    (initial produced middle final : ExecutionState) (values : List Carrier) (value : Carrier)
    (address : ExitAddress) (carriers : List Carrier)
    (normal : evalProduce fuel config environment [channel] operand initial = .ok values produced)
    (selected : singleCarrier values produced = .ok value middle)
    (escaped : evalOperands fuel config environment channels operands middle = .escape address carriers final) :
    evalOperands (fuel + 1) config environment (channel :: channels) (operand :: operands) initial =
      .escape address carriers final := by simp only [evalOperands, bind, normal, selected, escaped]

theorem operandsTail_stop_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channel : Channel) (channels : List Channel) (operand : Expr) (operands : List Expr)
    (initial produced middle final : ExecutionState) (values : List Carrier) (value : Carrier)
    (reason : Goose.Core.Stop)
    (normal : evalProduce fuel config environment [channel] operand initial = .ok values produced)
    (selected : singleCarrier values produced = .ok value middle)
    (stopped : evalOperands fuel config environment channels operands middle = .stop reason final) :
    evalOperands (fuel + 1) config environment (channel :: channels) (operand :: operands) initial =
      .stop reason final := by simp only [evalOperands, bind, normal, selected, stopped]

theorem statementsHead_escape_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (statement : Stmt) (statements : List Stmt) (initial final : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt fuel config environment statement initial = .escape address carriers final) :
    execStmts (fuel + 1) config environment (statement :: statements) initial = .escape address carriers final := by
  simp only [execStmts, bind, escaped]

theorem statementsHead_stop_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (statement : Stmt) (statements : List Stmt) (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (stopped : execStmt fuel config environment statement initial = .stop reason final) :
    execStmts (fuel + 1) config environment (statement :: statements) initial = .stop reason final := by
  simp only [execStmts, bind, stopped]

theorem statementsTail_escape_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (statement : Stmt) (statements : List Stmt) (initial middle final : ExecutionState) (value : Value)
    (address : ExitAddress) (carriers : List Carrier)
    (normal : execStmt fuel config environment statement initial = .ok (.normal value) middle)
    (escaped : execStmts fuel config environment statements middle = .escape address carriers final) :
    execStmts (fuel + 1) config environment (statement :: statements) initial = .escape address carriers final := by
  simp only [execStmts, bind, normal, escaped]

theorem statementsTail_stop_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (statement : Stmt) (statements : List Stmt) (initial middle final : ExecutionState) (value : Value)
    (reason : Goose.Core.Stop)
    (normal : execStmt fuel config environment statement initial = .ok (.normal value) middle)
    (stopped : execStmts fuel config environment statements middle = .stop reason final) :
    execStmts (fuel + 1) config environment (statement :: statements) initial = .stop reason final := by
  simp only [execStmts, bind, normal, stopped]

#print axioms ValueInvocationEdge.stop
#print axioms operandsHead_escape_after_child
#print axioms operandsHead_stop_after_child
#print axioms operandsTail_escape_after_child
#print axioms operandsTail_stop_after_child
#print axioms statementsHead_escape_after_child
#print axioms statementsHead_stop_after_child
#print axioms statementsTail_escape_after_child
#print axioms statementsTail_stop_after_child

end Goose.Proofs.ExitExecution
