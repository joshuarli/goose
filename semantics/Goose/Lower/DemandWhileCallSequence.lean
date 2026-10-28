import Goose.Lower.DemandWhileCallAgreement
import Goose.Lower.DemandCallReachableMixedRecursive

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

inductive ReachableCallLoopMixedCursor {cfg : Cfg} {env : Env} (caller : Func) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | existing {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ReachableWhileCallStatementCursor caller results selected source before built initial start map required runtime) :
      ReachableCallLoopMixedCursor caller results selected source before built initial start map required runtime
  | loop {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : WhileCallStatementCursor caller results selected source before built initial start map required runtime) :
      ReachableCallLoopMixedCursor caller results selected source before built initial start map required runtime

theorem accepted_generated_reachable_while_call_between_mixed {cfg : Cfg} {env : Env}
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
      CallMixedStoppedArguments argumentSource.rootsEnv.access arguments)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)
    {earlier later : List Stmt} (prefixForm : WhileMixedStatements cfg env earlier)
    (tailForm : ReachableMixedCallStatements cfg env later) :
    ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block
      (earlier ++ (.while condition body origin :: later))
      (@ReachableCallLoopMixedCursor cfg env caller results root owner selected) ∧
    ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block
      (earlier ++ (.while condition body origin :: later)) := by
  have suffix := accepted_generated_reachable_mixed_call_statements tailForm selected before bindings want block
  have mapped : ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block later
      (@ReachableCallLoopMixedCursor cfg env caller results root owner selected) :=
    ReachableSequencePrefixFamily.mapCursor
      (cursor := @ReachableWhileCallStatementCursor cfg env caller results root owner selected)
      (next := @ReachableCallLoopMixedCursor cfg env caller results root owner selected)
      (selected := selected) (before := before) (loop := none) (bindings := bindings) (want := want) (block := block) (statements := later)
      (fun {state} => suffix.1 (state := state)) (by
        intro statement state source before built initial start map required runtime cursor
        exact .existing cursor)
  have agreement := accepted_generated_while_call_agreement selected condition body origin conditionForm bodyStatements noValue
    contextAt implAt depth fragment form hasValue shrink argumentsForm stoppedArgumentsForm
  have head : ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none (.while condition body origin)
      (@ReachableCallLoopMixedCursor cfg env caller results root owner selected) :=
    ReachableStatementPrefixFamily.mapCursor
      (cursor := @WhileCallStatementCursor cfg env caller results root owner selected)
      (next := @ReachableCallLoopMixedCursor cfg env caller results root owner selected)
      (selected := selected) (loop := none) (statement := .while condition body origin)
      (fun {state} => agreement.1 (state := state)) (by
        intro statement state source before built initial start map required runtime cursor
        exact .loop cursor)
  have called : ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block
      (.while condition body origin :: later) (@ReachableCallLoopMixedCursor cfg env caller results root owner selected) ∧
    ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block
      (.while condition body origin :: later) :=
    ⟨accepted_generated_reachable_sequence_prefix_cons selected before none bindings want block _ head mapped,
      accepted_generated_reachable_stopped_sequence_cons selected before none bindings want block
        (fun {state} => agreement.2 (state := state)) (fun {state} => suffix.2 (state := state))⟩
  exact accepted_generated_invariant_while_mixed_prepend prefixForm
    (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) (results := results) selected before bindings want block
    (@ReachableCallLoopMixedCursor cfg env caller results root owner selected)
    (by intro statement state source before built initial start map required runtime cursor; exact .existing (.existing cursor))
    (fun point => RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point.point point.frame point.state)
    (fun valid steps => steps.reachable valid) called

#print axioms accepted_generated_reachable_while_call_between_mixed
end Goose.Lower
