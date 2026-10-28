import Goose.Lower.DemandWhileCallStoppedFamily
import Goose.Lower.DemandControlStatementAgreement

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_call_agreement {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (condition : Expr) (body : Core.Block) (origin : OriginId) (conditionForm : ControlPrefixExpression condition)
    {callContext : ContextId} {arguments : List Arg} {callOrigin statementOrigin : OriginId}
    (bodyStatements : body.stmts = [.expr (.call callContext arguments callOrigin) statementOrigin]) (noValue : body.value = none)
    {calleeContext : Context} {callee : Impl} (contextAt : cfg.mod.contexts[callContext]? = some calleeContext)
    (implAt : cfg.mod.impls[calleeContext.impl]? = some callee) (depth : env.depth < maxCallDepth)
    (fragment : ∀ current : St, WhileMixedStatements cfg
      { vars := callee.vars, act := current.nextAct, scopes := (callee.body.scope, current.nextScope) :: [], depth := env.depth + 1 } callee.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : callee.body.value = some expression)
    (shrink : cfg.mod.profile = .shrink)
    (argumentsForm : ∀ (middle : St) {innerState : St} (argumentSource : StmtSource cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } (.expr (.call callContext arguments callOrigin) statementOrigin) innerState),
      CallMixedArguments argumentSource.rootsEnv.access arguments)
    (stoppedArgumentsForm : ∀ (middle : St) {innerState : St} (argumentSource : StmtSource cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } (.expr (.call callContext arguments callOrigin) statementOrigin) innerState),
      CallMixedStoppedArguments argumentSource.rootsEnv.access arguments) :
    ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none (.while condition body origin)
      (@WhileCallStatementCursor cfg env caller results root owner selected) ∧
    ReachableStoppedStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none (.while condition body origin) :=
  ⟨accepted_generated_while_call_prefix_family selected condition body origin bodyStatements noValue contextAt implAt depth fragment form hasValue
      shrink argumentsForm stoppedArgumentsForm (accepted_generated_control_progress_prefix_family selected none conditionForm),
    accepted_generated_while_call_stopped_family selected condition body origin bodyStatements noValue contextAt implAt depth fragment form hasValue
      shrink argumentsForm stoppedArgumentsForm (accepted_generated_read_stopped_expressions selected none conditionForm.stopped)⟩

#print axioms accepted_generated_while_call_agreement
end Goose.Lower
