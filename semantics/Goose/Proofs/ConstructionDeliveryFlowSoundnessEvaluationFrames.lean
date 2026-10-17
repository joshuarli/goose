import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesValues
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesProduce
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesBuild
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesStatements
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesCalls

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationBreakFrames_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) : EvaluationBreakFrames (fuel + 1) config := by
  constructor
  · exact evalValue_breakFrame_succ fuel config previous
  · exact evalBound_breakFrame_succ fuel config previous
  · exact evalPlace_breakFrame_succ fuel config previous
  · exact evalView_breakFrame_succ fuel config previous
  · exact evalProduce_breakFrame_succ fuel config previous
  · exact evalOperands_breakFrame_succ fuel config previous
  · exact buildExpr_breakFrame_succ fuel config previous
  · exact buildElement_breakFrame_succ fuel config previous
  · exact evalArguments_breakFrame_succ fuel config previous
  · exact invokeCall_breakFrame_succ fuel config previous
  · exact enterActivation_breakFrame_succ fuel config previous
  · exact execActivationBody_breakFrame_succ fuel config previous
  · exact execResultBlock_breakFrame_succ fuel config previous
  · exact execResultBlockWith_breakFrame_succ fuel config previous
  · exact execBlock_breakFrame_succ fuel config previous
  · exact execStmts_breakFrame_succ fuel config previous
  · exact execStmt_breakFrame_succ fuel config previous
  · exact evalPrintArg_breakFrame_succ fuel config previous
  · exact execWhile_breakFrame_succ fuel config previous
  · exact execRange_breakFrame_succ fuel config previous
  · exact execEach_breakFrame_succ fuel config previous
  · exact loopBody_breakFrame_succ fuel config previous
  · exact pushValue_breakFrame_succ fuel config previous

theorem evaluationBreakFrames (fuel : Nat) (config : EvalConfig) : EvaluationBreakFrames fuel config := by
  induction fuel with
  | zero => exact evaluationBreakFrames_zero config
  | succ fuel previous => exact evaluationBreakFrames_succ fuel config previous

theorem initGlobals_breakFrame (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId) :
    BreakFrameAction (initGlobals fuel config globals) := by
  have previous := evaluationBreakFrames fuel config
  induction globals with
  | nil => exact breakFrame_pure _
  | cons global globals ih =>
    simp only [initGlobals]
    evaluation_frame previous

theorem runModule_breakFrame (fuel : Nat) (config : EvalConfig) :
    BreakFrameAction (runModule fuel config) := by
  have previous := evaluationBreakFrames fuel config
  unfold runModule
  apply breakFrame_bind
  · exact initGlobals_breakFrame fuel config _
  · intro _
    evaluation_frame previous

end Goose.Proofs.ConstructionDelivery
