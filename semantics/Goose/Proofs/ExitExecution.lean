import Goose.Proofs.ExitExecutionEvaluationStatements

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem evaluation_preservesFresh (fuel : Nat) (config : EvalConfig) :
    EvaluationPreservesFresh fuel config := by
  induction fuel with
  | zero => exact evaluationPreservesFresh_zero config
  | succ fuel previous =>
      refine {
        value := evalValue_preservesFresh_succ fuel config previous
        bound := evalBound_preservesFresh_succ fuel config previous
        place := evalPlace_preservesFresh_succ fuel config previous
        view := evalView_preservesFresh_succ fuel config previous
        produce := evalProduce_preservesFresh_succ fuel config previous
        operands := evalOperands_preservesFresh_succ fuel config previous
        build := buildExpr_preservesFresh_succ fuel config previous
        element := buildElement_preservesFresh_succ fuel config previous
        arguments := evalArguments_preservesFresh_succ fuel config previous
        call := invokeCall_preservesFresh_succ fuel config previous
        activation := enterActivation_preservesFresh_succ fuel config previous
        activationBody := ?_
        resultBlock := execResultBlock_preservesFresh_succ fuel config previous
        resultBlockWith := execResultBlockWith_preservesFresh_succ fuel config previous
        block := execBlock_preservesFresh_succ fuel config previous
        statements := execStmts_preservesFresh_succ fuel config previous
        statement := execStmt_preservesFresh_succ fuel config previous
        printArgument := evalPrintArg_preservesFresh_succ fuel config previous
        whileLoop := execWhile_preservesFresh_succ fuel config previous
        rangeLoop := execRange_preservesFresh_succ fuel config previous
        eachLoop := execEach_preservesFresh_succ fuel config previous
        loop := loopBody_preservesFresh_succ fuel config previous
        push := pushValue_preservesFresh_succ fuel config previous }
      intro environment pre body
      exact execActivationBody_preservesFresh_succ fuel config previous environment pre body

theorem initGlobals_preservesFresh (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId) :
    PreservesFresh (initGlobals fuel config globals) := by
  have previous := evaluation_preservesFresh fuel config
  induction globals with
  | nil => simpa only [initGlobals] using preservesFresh_pure ()
  | cons global globals preserved =>
      simp only [initGlobals]
      fresh_eval previous

theorem runModule_preservesFresh (fuel : Nat) (config : EvalConfig) :
    PreservesFresh (runModule fuel config) := by
  have previous := evaluation_preservesFresh fuel config
  unfold runModule
  apply preservesFresh_bind
  · exact initGlobals_preservesFresh _ _ _
  · intro _
    fresh_eval previous

theorem runModule_freshActivations (fuel : Nat) (config : EvalConfig) :
    FreshActivations (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) :=
  runModule_preservesFresh fuel config .initial freshActivations_initial

theorem runModule_selectedTarget_nearest (fuel : Nat) (config : EvalConfig) (targetId : Nat)
    (activation : RuntimeActivation) (final : ExecutionState)
    (selected : targetActivation config targetId
      (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) = .ok activation final) :
    final = Goose.Proofs.Exit.stepState (runModule fuel config .initial) ∧
    activation.act < final.nextAct ∧
    ∃ target discarded outer,
      config.module.targets[targetId]? = some target ∧
      final.activations = discarded ++ activation :: outer ∧
      target.contains activation.implementation = true ∧
      (∀ earlier ∈ discarded, target.contains earlier.implementation = false) ∧
      (final.activations.map (·.act)).Nodup := by
  obtain ⟨unchanged, target, discarded, outer, declared, shape, member, excluded⟩ :=
    targetActivation_selects_nearest config targetId _ final activation selected
  subst final
  obtain ⟨distinct, allocated⟩ := runModule_freshActivations fuel config
  have present : activation ∈
      (Goose.Proofs.Exit.stepState (runModule fuel config .initial)).activations := by
    rw [shape]
    simp
  exact ⟨rfl, allocated activation present, target, discarded, outer, declared, shape,
    member, excluded, distinct⟩

#print axioms runModule_freshActivations
#print axioms runModule_selectedTarget_nearest

end Goose.Proofs.ExitExecution
