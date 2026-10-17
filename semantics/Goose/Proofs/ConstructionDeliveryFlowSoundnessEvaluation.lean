import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatements
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationValues
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationProduce
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationProduceBuild
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationCalls
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationPush
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationLoops
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationBlocks
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationResultBlocks

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationControlFlows_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) : EvaluationControlFlows (fuel + 1) config := by
  refine {
    value := evaluationControl_value_succ fuel config previous
    bound := evaluationControl_bound_succ fuel config previous
    place := evaluationControl_place_succ fuel config previous
    view := evaluationControl_view_succ fuel config previous
    produce := evaluationControl_produce_succ fuel config previous
    operands := evaluationControl_operands_succ fuel config previous
    build := evaluationControl_build_succ fuel config previous
    element := evaluationControl_element_succ fuel config previous
    arguments := evaluationControl_arguments_succ fuel config previous
    call := evaluationControl_call_succ fuel config previous
    resultBlock := evaluationControl_resultBlock_succ fuel config previous
    resultBlockWith := evaluationControl_resultBlockWith_succ fuel config previous
    block := evaluationControl_block_succ fuel config previous
    statements := evaluationControl_statements_succ fuel config previous
    statement := evaluationControl_statement_succ fuel config previous
    printArgument := evaluationControl_printArgument_succ fuel config previous
    whileLoop := evaluationControl_while_succ fuel config previous
    rangeLoop := evaluationControl_range_succ fuel config previous
    eachLoop := evaluationControl_each_succ fuel config previous
    loop := evaluationControl_loop_succ fuel config previous
    loopIteration := evaluationControl_loopIteration_succ fuel config previous
    push := evaluationControl_push_succ fuel config previous
  }

theorem evaluationControlFlows (fuel : Nat) (config : EvalConfig) : EvaluationControlFlows fuel config := by
  induction fuel with
  | zero => exact evaluationControlFlows_zero config
  | succ fuel previous => exact evaluationControlFlows_succ fuel config previous

#print axioms evaluationControlFlows

end Goose.Proofs.ConstructionDelivery
