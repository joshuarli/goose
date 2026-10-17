import Goose.Proofs.ExitExecutionActivationChannelsInvocation
import Goose.Proofs.ExitExecutionActivationChannelsStatements
import Goose.Proofs.ExitExecutionActivationChannelsBuild

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem evaluationActivationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) :
    EvaluationActivationChannels (fuel + 1) config := by
  refine {
    value := evalValue_activationChannels_succ fuel config previousFresh previous
    bound := evalBound_activationChannels_succ fuel config previousFresh previous
    place := evalPlace_activationChannels_succ fuel config previousFresh previous
    view := evalView_activationChannels_succ fuel config previousFresh previous
    produce := evalProduce_activationChannels_succ fuel config previousFresh previous
    operands := evalOperands_activationChannels_succ fuel config previousFresh previous
    build := buildExpr_activationChannels_succ fuel config previousFresh previous
    element := buildElement_activationChannels_succ fuel config previousFresh previous
    arguments := evalArguments_activationChannels_succ fuel config previousFresh previous
    call := invokeCall_activationChannels_succ fuel config previousFresh previous
    activation := enterActivation_activationChannels_succ fuel config previousFresh previous
    activationBody := execActivationBody_activationChannels_succ fuel config previousFresh previous
    resultBlock := execResultBlock_activationChannels_succ fuel config previousFresh previous
    resultBlockWith := execResultBlockWith_activationChannels_succ fuel config previousFresh previous
    block := execBlock_activationChannels_succ fuel config previousFresh previous
    statements := execStmts_activationChannels_succ fuel config previousFresh previous
    statement := execStmt_activationChannels_succ fuel config previousFresh previous
    printArgument := evalPrintArg_activationChannels_succ fuel config previousFresh previous
    whileLoop := execWhile_activationChannels_succ fuel config previousFresh previous
    rangeLoop := execRange_activationChannels_succ fuel config previousFresh previous
    eachLoop := execEach_activationChannels_succ fuel config previousFresh previous
    loop := loopBody_activationChannels_succ fuel config previousFresh previous
    push := pushValue_activationChannels_succ fuel config previousFresh previous }

theorem evaluationActivationChannels (fuel : Nat) (config : EvalConfig) :
    EvaluationActivationChannels fuel config := by
  induction fuel with
  | zero => exact evaluationActivationChannels_zero config
  | succ fuel previous =>
      exact evaluationActivationChannels_succ fuel config (evaluation_preservesFresh fuel config) previous

theorem initGlobals_activationChannels (fuel : Nat) (config : EvalConfig)
    (globals : List Goose.Core.GlobalId) :
    PreservesActivationChannels (initGlobals fuel config globals) := by
  have previousFresh := evaluation_preservesFresh fuel config
  have previous := evaluationActivationChannels fuel config
  induction globals with
  | nil => simp only [initGlobals]; exact preservesActivationChannels_pure ()
  | cons global globals inductionHypothesis =>
      simp only [initGlobals]
      activation_channels_construction_eval previousFresh previous config

theorem runModule_activationChannels (fuel : Nat) (config : EvalConfig) :
    PreservesActivationChannels (runModule fuel config) := by
  have previousFresh := evaluation_preservesFresh fuel config
  have previous := evaluationActivationChannels fuel config
  unfold runModule
  apply preservesActivationChannels_bind (initGlobals fuel config _) _
  · exact initGlobals_activationChannels fuel config _
  · exact initGlobals_preservesFresh fuel config _
  · intro _
    activation_channels_helper_eval previousFresh previous config

theorem runModule_initial_activationChannels (fuel : Nat) (config : EvalConfig) :
    ActivationChannelsOutcome [] (runModule fuel config ExecutionState.initial) := by
  simpa [ActivationChannelsProjection, ExecutionState.initial] using
    runModule_activationChannels fuel config ExecutionState.initial freshActivations_initial

end Goose.Proofs.ExitExecution
