import Goose.Lower.DemandWhileCallStoppedFamily
import Goose.Lower.DemandControlStatementAgreement

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_scalar_call_agreement {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (condition : Expr) (body : Core.Block) (origin : OriginId) (conditionForm : ControlPrefixExpression condition)
    (fragment : ∀ middle : St, ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
    (noValue : body.value = none) :
    ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none (.while condition body origin)
      (@WhileCallStatementCursor cfg env caller results root owner selected) ∧
    ReachableStoppedStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none (.while condition body origin) :=
  ⟨accepted_generated_while_scalar_call_prefix_family selected condition body origin fragment noValue (accepted_generated_control_progress_prefix_family selected none conditionForm),
    accepted_generated_while_scalar_call_stopped_family selected condition body origin fragment noValue (accepted_generated_read_stopped_expressions selected none conditionForm.stopped)⟩

#print axioms accepted_generated_while_scalar_call_agreement
end Goose.Lower
