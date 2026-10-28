import Goose.Proofs.ConstructionActivationCounterStatementCases

set_option Elab.async false

namespace Goose.Proofs.ConstructionActivationCounterEvaluation
open Goose.Construct Goose.Proofs.ConstructionActivationCounter
open Goose.Proofs.ConstructionActivationCounterOwner Goose.Proofs.ConstructionActivationCounterStatements

theorem execStmt_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (statement : Stmt) :
    PreservesActivationCounter (execStmt (fuel + 1) config environment statement) := by
  cases statement with
  | letS x e org => exact execStmt_letS_counter_succ fuel config previous environment x e org
  | assign p e org => exact execStmt_assign_counter_succ fuel config previous environment p e org
  | assignOp op p e org => exact execStmt_assignOp_counter_succ fuel config previous environment op p e org
  | rebind x e org => exact execStmt_rebind_counter_succ fuel config previous environment x e org
  | expr e org => exact execStmt_expr_counter_succ fuel config previous environment e org
  | append p v org => exact execStmt_append_counter_succ fuel config previous environment p v org
  | popN p e org => exact execStmt_popN_counter_succ fuel config previous environment p e org
  | resize p e fill org => exact execStmt_resize_counter_succ fuel config previous environment p e fill org
  | clear p org => exact execStmt_clear_counter_succ fuel config previous environment p org
  | assignWhole p e org => exact execStmt_assignWhole_counter_succ fuel config previous environment p e org
  | ifS c a b org => exact execStmt_ifS_counter_succ fuel config previous environment c a b org
  | «while» c b org => exact execStmt_while_counter_succ fuel config previous environment c b org
  | forRange x lo hi b org => exact execStmt_forRange_counter_succ fuel config previous environment x lo hi b org
  | forEach x index v byRef b org => exact execStmt_forEach_counter_succ fuel config previous environment x index v byRef b org
  | receive vars e org => exact execStmt_receive_counter_succ fuel config previous environment vars e org
  | appendValue p e org => exact execStmt_appendValue_counter_succ fuel config previous environment p e org
  | appendConstruct p e org => exact execStmt_appendConstruct_counter_succ fuel config previous environment p e org
  | retValues es org => exact execStmt_retValues_counter_succ fuel config previous environment es org
  | retForward e org => exact execStmt_retForward_counter_succ fuel config previous environment e org
  | returnFrom target es org => exact execStmt_returnFrom_counter_succ fuel config previous environment target es org
  | returnFromForward target e org => exact execStmt_returnFromForward_counter_succ fuel config previous environment target e org
  | breakValue e org => exact execStmt_breakValue_counter_succ fuel config previous environment e org
  | ret e org => exact execStmt_ret_counter_succ fuel config previous environment e org
  | brk org => exact execStmt_brk_counter_succ fuel config previous environment org
  | cont org => exact execStmt_cont_counter_succ fuel config previous environment org
  | print args org => exact execStmt_print_counter_succ fuel config previous environment args org
  | assertS e org => exact execStmt_assertS_counter_succ fuel config previous environment e org
  | abort msg org => exact execStmt_abort_counter_succ fuel config previous environment msg org
  | exit e org => exact execStmt_exit_counter_succ fuel config previous environment e org

theorem evaluation_preservesActivationCounter (fuel : Nat) (config : EvalConfig) :
    EvaluationPreservesActivationCounter fuel config := by
  induction fuel with
  | zero => exact evaluationCounter_zero config
  | succ fuel previous =>
      refine {
        value := evalValue_counter_succ fuel config previous
        bound := evalBound_counter_succ fuel config previous
        place := evalPlace_counter_succ fuel config previous
        view := evalView_counter_succ fuel config previous
        produce := evalProduce_counter_succ fuel config previous
        operands := evalOperands_counter_succ fuel config previous
        build := buildExpr_counter_succ fuel config previous
        element := buildElement_counter_succ fuel config previous
        arguments := evalArguments_counter_succ fuel config previous
        call := invokeCall_counter_succ fuel config previous
        activation := enterActivation_counter_succ fuel config previous
        activationBody := ?_
        resultBlock := execResultBlock_counter_succ fuel config previous
        resultBlockWith := execResultBlockWith_counter_succ fuel config previous
        block := execBlock_counter_succ fuel config previous
        statements := execStmts_counter_succ fuel config previous
        statement := execStmt_counter_succ fuel config previous
        printArgument := evalPrintArg_counter_succ fuel config previous
        whileLoop := execWhile_counter_succ fuel config previous
        rangeLoop := execRange_counter_succ fuel config previous
        eachLoop := execEach_counter_succ fuel config previous
        loop := loopBody_counter_succ fuel config previous
        push := pushValue_counter_succ fuel config previous }
      intro environment pre body
      exact execActivationBody_counter_succ fuel config previous environment pre body

#print axioms evaluation_preservesActivationCounter
end Goose.Proofs.ConstructionActivationCounterEvaluation
