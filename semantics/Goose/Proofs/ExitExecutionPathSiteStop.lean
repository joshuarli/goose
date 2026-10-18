import Goose.Proofs.ExitExecutionPathDispatchUnwind
import Goose.Proofs.ExitExecutionPathSequenceUnwind
import Goose.Proofs.ExitExecutionPathProducerStop
import Goose.Proofs.ExitExecutionPathControlUnwind
import Goose.Proofs.ExitExecutionPathCompletionUnwind
import Goose.Proofs.ExitExecutionPathScopeStopForward
import Goose.Proofs.ExitExecutionPathStatementStops

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem stopFrame_exact {config : EvalConfig} {α β : Type}
    {parent : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (_site : ExitCallSite config parent initial child prepared)
    (before : ExecutionState) (reason : Goose.Core.Stop)
    (stopped : parent.action config initial = .stop reason before) :
    ∃ finalReason final changes, parent.action config initial = .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage :=
  ⟨reason, before, [], stopped, rfl, rfl, .refl _⟩

theorem ExitCallSite.stop_after_child {config : EvalConfig} {α β : Type}
    {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared before : ExecutionState} {reason : Goose.Core.Stop}
    (site : ExitCallSite config parent initial child prepared)
    (stopped : child.action config prepared = .stop reason before) :
    ∃ finalReason final changes, parent.action config initial = .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage := by
  have actualSite := site
  cases site
  case values edge =>
    exact stopFrame_exact actualSite before reason (edge.stop reason before stopped)
  case producer edge =>
    obtain ⟨final, returned, construction, objects⟩ := edge.stop_after_child stopped
    refine ⟨reason, final, [], returned, congrArg (fun state => state.stdout) construction, objects, ?_⟩
    rw [construction]
    exact .refl _
  case statements edge =>
    exact edge.stop_after_child stopped
  case completionProduce =>
    rename_i fuel environment incoming expression planned setup
    exact completionProduce_stop_after_child incoming (expressionOrigin expression)
      (fun channels => evalProduce fuel config environment channels expression)
      initial prepared before planned reason setup stopped
  case blockStatements =>
    obtain ⟨finalReason, final, returned, stdout, objects, storage⟩ :=
      ExitCallSite.blockStatements_stop_after_child actualSite (by assumption) stopped
    exact ⟨finalReason, final, [], returned, stdout, objects, storage⟩
  case blockValueTail =>
    obtain ⟨finalReason, final, returned, stdout, objects, storage⟩ :=
      ExitCallSite.blockValueTail_stop_after_child actualSite (by assumption) (by assumption) (by assumption) stopped
    exact ⟨finalReason, final, [], returned, stdout, objects, storage⟩
  case blockProduceTail =>
    obtain ⟨finalReason, final, returned, stdout, objects, storage⟩ :=
      ExitCallSite.blockProduceTail_stop_after_child actualSite (by assumption) (by assumption) (by assumption) stopped
    exact ⟨finalReason, final, [], returned, stdout, objects, storage⟩
  case activationStatements =>
    obtain ⟨finalReason, final, returned, stdout, objects, storage⟩ :=
      ExitCallSite.activationStatements_stop_after_child actualSite (by assumption) stopped
    exact ⟨finalReason, final, [], returned, stdout, objects, storage⟩
  case activationTail =>
    obtain ⟨finalReason, final, returned, stdout, objects, storage⟩ :=
      ExitCallSite.activationTail_stop_after_child actualSite (by assumption) (by assumption) stopped
    exact ⟨finalReason, final, [], returned, stdout, objects, storage⟩
  case resultStatements =>
    obtain ⟨finalReason, final, returned, stdout, objects, storage⟩ :=
      ExitCallSite.resultStatements_stop_after_child actualSite (by assumption) stopped
    exact ⟨finalReason, final, [], returned, stdout, objects, storage⟩
  case resultTail =>
    obtain ⟨finalReason, final, returned, stdout, objects, storage⟩ :=
      ExitCallSite.resultTail_stop_after_child actualSite (by assumption) (by assumption) stopped
    exact ⟨finalReason, final, [], returned, stdout, objects, storage⟩
  all_goals simp only [ExitInvocation.action] at stopped ⊢
  all_goals first
    | (apply returnOperands_stop_after_child <;> assumption)
    | (apply returnForwardProduce_stop_after_child <;> assumption)
    | (apply returnProduce_stop_after_child <;> assumption)
    | (apply breakProduce_stop_after_child <;> assumption)
    | (apply returnFromOperands_stop_after_child <;> assumption)
    | (apply returnFromForwardProduce_stop_after_child <;> assumption)
    | (apply stopFrame_exact actualSite
       first
         | (apply moduleGlobals_stop_after_child <;> assumption)
         | (apply moduleEntry_stop_after_child <;> assumption)
         | (apply CallArgumentPrefix.stop_call <;> assumption)
         | (apply CallActivationPrefix.stop_call <;> assumption)
         | (apply argumentReference_stop_after_child <;> assumption)
         | (apply argumentValue_stop_after_child <;> assumption)
         | (apply argumentMaterialize_stop_after_child <;> assumption)
         | (apply argumentBuild_stop_after_child <;> assumption)
         | (apply ArgumentValuePrefix.stop_arguments <;> assumption)
         | (apply operandsHead_stop_after_child <;> assumption)
         | (apply operandsTail_stop_after_child <;> assumption)
         | (apply statementsHead_stop_after_child <;> assumption)
         | (apply statementsTail_stop_after_child <;> assumption)
         | (apply activationScope_stop_after_child <;> assumption)
         | (apply resultBlockWith_stop_after_child <;> assumption)
         | (apply resultScope_stop_after_child <;> assumption)
         | (apply enterActivation_stop_after_body <;> assumption))

theorem ExitContextReached.stop_root {rootFuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {α : Type} {invocation : ExitInvocation α}
    {initial before : ExecutionState} {reason : Goose.Core.Stop}
    (reached : ExitContextReached rootFuel config context invocation initial)
    (stopped : invocation.action config initial = .stop reason before) :
    ∃ finalReason final changes, runModule rootFuel config .initial = .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage := by
  induction reached generalizing before reason with
  | initial => exact ⟨reason, before, [], stopped, rfl, rfl, .refl _⟩
  | call callerReached site frames previous =>
      obtain ⟨parentReason, parentFinal, first, parentStopped, parentStdout, parentObjects, parentStorage⟩ :=
        site.stop_after_child stopped
      obtain ⟨finalReason, final, remaining, rootStopped, stdout, objects, storage⟩ := previous parentStopped
      exact ⟨finalReason, final, first ++ remaining, rootStopped,
        stdout.trans parentStdout, objects.trans parentObjects, .append parentStorage storage⟩

#print axioms ExitContextReached.stop_root

#print axioms ExitCallSite.stop_after_child

end Goose.Proofs.ExitExecution
