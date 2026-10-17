import Goose.Proofs.ConstructionExecutionProtocolEvaluationControl

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

variable {predicate : ConstructionState → Prop} [primitives : ConstructionProtocolPrimitives predicate]
  [reservations : ConstructionReservationPrimitives predicate]
include primitives reservations

theorem evaluation_preservesConstructionInvariant (fuel : Nat) (config : EvalConfig) :
    (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config := by
  induction fuel with
  | zero => exact evaluationPreservesConstructionInvariant_zero config
  | succ fuel previous =>
      refine {
        value := evalValue_preservesConstructionInvariant_succ fuel config previous
        bound := evalBound_preservesConstructionInvariant_succ fuel config previous
        place := evalPlace_preservesConstructionInvariant_succ fuel config previous
        view := evalView_preservesConstructionInvariant_succ fuel config previous
        produce := evalProduce_preservesConstructionInvariant_succ fuel config previous
        operands := evalOperands_preservesConstructionInvariant_succ fuel config previous
        build := buildExpr_preservesConstructionInvariant_succ fuel config previous
        element := buildElement_preservesConstructionInvariant_succ fuel config previous
        arguments := evalArguments_preservesConstructionInvariant_succ fuel config previous
        call := invokeCall_preservesConstructionInvariant_succ fuel config previous
        activation := enterActivation_preservesConstructionInvariant_succ fuel config previous
        activationBody := ?_
        resultBlock := execResultBlock_preservesConstructionInvariant_succ fuel config previous
        resultBlockWith := execResultBlockWith_preservesConstructionInvariant_succ fuel config previous
        block := execBlock_preservesConstructionInvariant_succ fuel config previous
        statements := execStmts_preservesConstructionInvariant_succ fuel config previous
        statement := execStmt_preservesConstructionInvariant_succ fuel config previous
        printArgument := evalPrintArg_preservesConstructionInvariant_succ fuel config previous
        whileLoop := execWhile_preservesConstructionInvariant_succ fuel config previous
        rangeLoop := execRange_preservesConstructionInvariant_succ fuel config previous
        eachLoop := execEach_preservesConstructionInvariant_succ fuel config previous
        loop := loopBody_preservesConstructionInvariant_succ fuel config previous
        push := pushValue_preservesConstructionInvariant_succ fuel config previous }
      intro environment pre body
      exact execActivationBody_preservesConstructionInvariant_succ fuel config previous environment pre body

theorem initGlobals_preservesConstructionInvariant (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId) :
    (PreservesConstructionInvariant predicate) (initGlobals fuel config globals) := by
  have previous := evaluation_preservesConstructionInvariant (predicate := predicate) fuel config
  induction globals with
  | nil => simpa only [initGlobals] using preservesConstructionInvariant_pure ()
  | cons global globals preserved =>
      simp only [initGlobals]
      protocol_eval previous

theorem runModule_preservesConstructionInvariant (fuel : Nat) (config : EvalConfig) :
    (PreservesConstructionInvariant predicate) (runModule fuel config) := by
  have previous := evaluation_preservesConstructionInvariant (predicate := predicate) fuel config
  unfold runModule
  apply preservesConstructionInvariant_bind
  · exact initGlobals_preservesConstructionInvariant _ _ _
  · intro _
    protocol_eval previous

end Goose.Proofs.ConstructionExecutionProtocol
