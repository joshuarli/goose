import Goose.Lower.DemandCallReachableMixed

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

inductive ReachableMixedCallStatements (cfg : Cfg) (env : Env) : List Stmt → Prop
  | mixed {statements : List Stmt} (fragment : WhileMixedStatements cfg env statements) :
      ReachableMixedCallStatements cfg env statements
  | call {earlier later : List Stmt} (earlierForm : WhileMixedStatements cfg env earlier)
      (context : ContextId) (arguments : List Arg) (origin statementOrigin : OriginId)
      (ctx : Context) (impl : Impl) (contextAt : cfg.mod.contexts[context]? = some ctx)
      (implAt : cfg.mod.impls[ctx.impl]? = some impl) (depth : env.depth < maxCallDepth)
      (fragment : ∀ middle : St, WhileMixedStatements cfg
        { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
      (expression : Expr) (form : ControlPrefixExpression expression) (hasValue : impl.body.value = some expression)
      (shrink : cfg.mod.profile = .shrink)
      (argumentsForm : ∀ {state : St} (source : StmtSource cfg env (.expr (.call context arguments origin) statementOrigin) state),
        CallMixedArguments source.rootsEnv.access arguments)
      (stoppedArgumentsForm : ∀ {state : St} (source : StmtSource cfg env (.expr (.call context arguments origin) statementOrigin) state),
        CallMixedStoppedArguments source.rootsEnv.access arguments)
      (tail : ReachableMixedCallStatements cfg env later) :
      ReachableMixedCallStatements cfg env (earlier ++ (.expr (.call context arguments origin) statementOrigin :: later))

theorem accepted_generated_reachable_mixed_call_statements {cfg : Cfg} {env : Env} {statements : List Stmt}
    (fragment : ReachableMixedCallStatements cfg env statements) :
    ∀ {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
      (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
      (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block),
      ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block statements
        (@ReachableWhileCallStatementCursor cfg env caller results root owner selected) ∧
      ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block statements := by
  induction fragment with
  | @mixed segment fragment =>
    intro caller results root owner selected before bindings want block
    have original := accepted_generated_while_mixed_statements fragment
      (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) (results := results) selected before bindings want block
    have mapped : GeneratedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block segment
        (@ReachableWhileCallStatementCursor cfg env caller results root owner selected) :=
      GeneratedSequencePrefixFamily.mapCursor
        (cursor := @WhileMixedStatementCursor cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results root owner selected)
        (next := @ReachableWhileCallStatementCursor cfg env caller results root owner selected)
        (selected := selected) (before := before) (loop := none) (bindings := bindings) (want := want) (block := block) (statements := segment)
        (fun {state} => original.1 (state := state)) (by
          intro statement state source before built initial start map required runtime cursor
          exact .existing cursor)
    exact ⟨mapped.reachable, GeneratedStoppedSequencePrefixFamily.reachable (selected := selected) (before := before) (loop := none)
      (bindings := bindings) (want := want) (block := block) (statements := segment) (fun {state} => original.2 (state := state))⟩
  | @call earlier later earlierForm context arguments origin statementOrigin ctx impl contextAt implAt depth callee expression form hasValue shrink argumentsForm stoppedArgumentsForm tail ih =>
    intro caller results root owner selected before bindings want block
    have suffix := ih selected before bindings want block
    have head : ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none
        (.expr (.call context arguments origin) statementOrigin)
        (@ReachableWhileCallStatementCursor cfg env caller results root owner selected) :=
      ReachableStatementPrefixFamily.mapCursor
        (cursor := @ReachableCallStatementFamilyCursor cfg env caller results none)
        (next := @ReachableWhileCallStatementCursor cfg env caller results root owner selected)
        (selected := selected) (loop := none) (statement := .expr (.call context arguments origin) statementOrigin)
        (accepted_generated_reachable_control_call_statement_family contextAt implAt depth callee form hasValue
          shrink argumentsForm selected none) (by
            intro statement state source before built initial start map required runtime cursor
            exact .call cursor)
    have called : ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block
        (.expr (.call context arguments origin) statementOrigin :: later)
        (@ReachableWhileCallStatementCursor cfg env caller results root owner selected) ∧
      ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block
        (.expr (.call context arguments origin) statementOrigin :: later) := ⟨accepted_generated_reachable_sequence_prefix_cons selected before none bindings want block _ head suffix.1,
      accepted_generated_reachable_stopped_sequence_cons selected before none bindings want block
        (accepted_generated_reachable_control_call_statement_stopped_family contextAt implAt depth callee form hasValue
          shrink stoppedArgumentsForm selected none) suffix.2⟩
    exact accepted_generated_invariant_while_mixed_prepend earlierForm
      (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) (results := results) selected before bindings want block
      (@ReachableWhileCallStatementCursor cfg env caller results root owner selected)
      (by intro statement state source before built initial start map required runtime cursor; exact .existing cursor)
      (fun point => RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point.point point.frame point.state)
      (fun valid steps => steps.reachable valid) called

#print axioms accepted_generated_reachable_mixed_call_statements
end Goose.Lower
