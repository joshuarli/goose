import Goose.Proofs.ExitExecutionInvocationStatementsCausal
import Goose.Proofs.ExitExecutionInvocationStatementsEscape

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem statementInvocation_escape_cause (config : EvalConfig)
    {α : Type} (parent : ExitInvocation α) (source : StatementInvocationSource parent)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : parent.action config initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared before : ExecutionState)
      (edge : StatementInvocationEdge config parent initial child prepared),
      child.action config prepared = .escape address carriers before ∧
        StatementInvocationUnwinds config address carriers before edge (.escape address carriers final) := by
  obtain ⟨β, child, prepared, before, edge, failure⟩ :=
    statementInvocation_escape_inv config parent source initial final address carriers escaped
  refine ⟨β, child, prepared, before, edge, failure, ?_⟩
  simpa only [escaped] using edge.propagates config address carriers failure

end Goose.Proofs.ExitExecution
