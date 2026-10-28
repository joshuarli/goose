import Goose.Lower.DemandWhilePrefixFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_agreement {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (condition : Expr) (body : Core.Block) (origin : OriginId)
    (form : ControlPrefixExpression condition)
    (fragment : ∀ middle : St, RecursiveIfStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
    (noValue : body.value = none) :
    GeneratedStatementPrefixFamily cx results selected none (.while condition body origin)
      (@WhileStatementPrefixCursor cfg env cx results root owner selected) ∧
    GeneratedStoppedStatementPrefixFamily cx results selected none (.while condition body origin) :=
  ⟨accepted_generated_while_prefix_family selected condition body origin fragment noValue
      (accepted_generated_control_prefix_family selected none form),
    accepted_generated_while_stopped_family selected condition body origin fragment noValue
      (accepted_generated_read_stopped_expressions selected none form.stopped)⟩

#print axioms accepted_generated_while_agreement
end Goose.Lower
