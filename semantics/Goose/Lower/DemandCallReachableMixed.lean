import Goose.Lower.DemandCallReachableSequence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_reachable_control_call_between_mixed {cfg : Cfg} {env : Env}
    {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl) (depth : env.depth < maxCallDepth)
    (fragment : ∀ middle : St, WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : impl.body.value = some expression)
    (shrink : cfg.mod.profile = .shrink)
    (argumentsForm : ∀ {state : St} (source : StmtSource cfg env (.expr (.call context arguments origin) statementOrigin) state),
      CallMixedArguments source.rootsEnv.access arguments)
    (stoppedArgumentsForm : ∀ {state : St} (source : StmtSource cfg env (.expr (.call context arguments origin) statementOrigin) state),
      CallMixedStoppedArguments source.rootsEnv.access arguments)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)
    {earlier later : List Stmt} (prefixForm : WhileMixedStatements cfg env earlier) (tailForm : WhileMixedStatements cfg env later) :
    ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block
      (earlier ++ (.expr (.call context arguments origin) statementOrigin :: later))
      (@ReachableWhileCallStatementCursor cfg env caller results root owner selected) ∧
    ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block
      (earlier ++ (.expr (.call context arguments origin) statementOrigin :: later)) := by
  have tail := accepted_generated_reachable_control_call_while_tail contextAt implAt depth fragment form hasValue shrink
    argumentsForm stoppedArgumentsForm selected before bindings want block tailForm
  exact accepted_generated_invariant_while_mixed_prepend prefixForm
    (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) (results := results) selected before bindings want block
    (@ReachableWhileCallStatementCursor cfg env caller results root owner selected)
    (by
      intro statement state source before built initial start map required runtime cursor
      exact .existing cursor)
    (fun point => RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point.point point.frame point.state)
    (fun valid steps => steps.reachable valid) tail

#print axioms accepted_generated_reachable_control_call_between_mixed
end Goose.Lower
