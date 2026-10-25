import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsLet
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsReturns
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsBreak

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationControl_statement_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (statement : Stmt) (staticFuel : Nat) (enough : statementQueryBudget statement ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel statement) resultControlFlow
      (execStmt (fuel + 1) config environment statement) := by
  cases statement with
  | letS x e org => exact evaluationControl_statement_let_succ fuel config previous environment x e org staticFuel enough
  | assign p e org => exact evaluationControl_statement_assign_succ fuel config previous environment p e org staticFuel enough
  | assignOp op p e org => exact evaluationControl_statement_assignOp_succ fuel config previous environment op p e org staticFuel enough
  | rebind x e org => exact evaluationControl_statement_rebind_succ fuel config previous environment x e org staticFuel enough
  | expr e org => exact evaluationControl_statement_expr_succ fuel config previous environment e org staticFuel enough
  | append p v org => exact evaluationControl_statement_append_succ fuel config previous environment p v org staticFuel enough
  | popN p e org => exact evaluationControl_statement_popN_succ fuel config previous environment p e org staticFuel enough
  | resize p e fill org => exact evaluationControl_statement_resize_succ fuel config previous environment p e fill org staticFuel enough
  | clear p org => exact evaluationControl_statement_clear_succ fuel config previous environment p org staticFuel enough
  | assignWhole p e org => exact evaluationControl_statement_assignWhole_succ fuel config previous environment p e org staticFuel enough
  | ifS c a b org => exact evaluationControl_statement_if_succ fuel config previous environment c a b org staticFuel enough
  | «while» c b org => exact evaluationControl_statement_while_succ fuel config previous environment c b org staticFuel enough
  | forRange x lo hi b org => exact evaluationControl_statement_range_succ fuel config previous environment x lo hi b org staticFuel enough
  | forEach x index v byRef b org => exact evaluationControl_statement_each_succ fuel config previous environment x index v byRef b org staticFuel enough
  | receive vars e org => exact evaluationControl_statement_receive_succ fuel config previous environment vars e org staticFuel enough
  | appendValue p e org => exact evaluationControl_statement_appendValue_succ fuel config previous environment p e org staticFuel enough
  | appendConstruct p e org => exact evaluationControl_statement_appendConstruct_succ fuel config previous environment p e org staticFuel enough
  | retValues es org => exact evaluationControl_statement_retValues_succ fuel config previous environment es org staticFuel enough
  | retForward e org => exact evaluationControl_statement_retForward_succ fuel config previous environment e org staticFuel enough
  | returnFrom target es org => exact evaluationControl_statement_returnFrom_succ fuel config previous environment target es org staticFuel enough
  | returnFromForward target e org => exact evaluationControl_statement_returnFromForward_succ fuel config previous environment target e org staticFuel enough
  | breakValue e org => exact evaluationControl_statement_breakValue_succ fuel config previous environment e org staticFuel enough
  | ret e org => exact evaluationControl_statement_ret_succ fuel config previous environment e org staticFuel enough
  | brk org => exact evaluationControl_statement_break_succ fuel config environment org staticFuel enough
  | cont org => exact evaluationControl_statement_continue_succ fuel config environment org staticFuel enough
  | print args org => exact evaluationControl_statement_print_succ fuel config previous environment args org staticFuel enough
  | assertS e org => exact evaluationControl_statement_assert_succ fuel config previous environment e org staticFuel enough
  | abort msg org => exact evaluationControl_statement_abort_succ fuel config environment msg org staticFuel enough
  | exit e org => exact evaluationControl_statement_exit_succ fuel config previous environment e org staticFuel enough

#print axioms evaluationControl_statement_succ

end Goose.Proofs.ConstructionDelivery
