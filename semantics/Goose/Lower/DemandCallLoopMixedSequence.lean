import Goose.Lower.DemandCallReachableMixed
import Goose.Lower.DemandCallMixedNormal

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

inductive ReachableScalarCallStatements (cfg : Cfg) (env : Env) : List Stmt → Prop
  | mixed {statements : List Stmt} (fragment : ScalarAssignmentStatements cfg env statements) :
      ReachableScalarCallStatements cfg env statements
  | call {earlier later : List Stmt} (earlierForm : ScalarAssignmentStatements cfg env earlier)
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
      (tail : ReachableScalarCallStatements cfg env later) :
      ReachableScalarCallStatements cfg env (earlier ++ (.expr (.call context arguments origin) statementOrigin :: later))

inductive ReachableScalarCallCursor {cfg : Cfg} {env : Env} (caller : Func) (results : List Ty) (loop : Option LoopCtx) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | scalar {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ScalarAssignmentStatementPrefixCursor ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results source before built initial start map required runtime) :
      ReachableScalarCallCursor caller results loop source before built initial start map required runtime
  | call {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ReachableCallStatementFamilyCursor caller results loop source before built initial start map required runtime) :
      ReachableScalarCallCursor caller results loop source before built initial start map required runtime

theorem accepted_generated_reachable_scalar_call_statements {cfg : Cfg} {env : Env} {statements : List Stmt}
    (fragment : ReachableScalarCallStatements cfg env statements) :
    ∀ {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
      (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
      (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block),
      ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block statements
        (@ReachableScalarCallCursor cfg env caller results loop) ∧
      ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block statements := by
  induction fragment with
  | @mixed segment fragment =>
    intro caller results root owner selected before loop bindings want block
    have empty : ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block []
        (@ReachableScalarCallCursor cfg env caller results loop) ∧
      ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block [] := by
      constructor
      · exact GeneratedSequencePrefixFamily.reachable (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) (selected := selected) (before := before) (loop := loop) (bindings := bindings) (want := want) (block := block) (statements := []) (cursor := @ReachableScalarCallCursor cfg env caller results loop) (fun {state} => accepted_generated_sequence_prefix_nil selected before loop bindings want block _ (state := state))
      · exact GeneratedStoppedSequencePrefixFamily.reachable (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) (selected := selected) (before := before) (loop := loop) (bindings := bindings) (want := want) (block := block) (statements := []) (fun {state} => accepted_generated_stopped_sequence_nil selected before loop bindings want block (state := state))
    simpa using accepted_generated_invariant_scalar_assignment_statements_prepend selected before loop bindings want block fragment
      (@ReachableScalarCallCursor cfg env caller results loop)
      (by intro statement state source before built initial start map required runtime cursor; exact .scalar cursor)
      (fun point => RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point.point point.frame point.state)
      (fun valid steps => steps.reachable valid) empty
  | @call earlier later earlierForm context arguments origin statementOrigin ctx impl contextAt implAt depth callee expression form hasValue shrink argumentsForm stoppedArgumentsForm tail ih =>
    intro caller results root owner selected before loop bindings want block
    have suffix := ih selected before loop bindings want block
    have head : ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop
        (.expr (.call context arguments origin) statementOrigin)
        (@ReachableScalarCallCursor cfg env caller results loop) :=
      ReachableStatementPrefixFamily.mapCursor
        (cursor := @ReachableCallStatementFamilyCursor cfg env caller results loop)
        (next := @ReachableScalarCallCursor cfg env caller results loop)
        (selected := selected) (loop := loop) (statement := .expr (.call context arguments origin) statementOrigin)
        (accepted_generated_reachable_control_call_statement_family contextAt implAt depth callee form hasValue
          shrink argumentsForm selected loop) (by
            intro statement state source before built initial start map required runtime cursor
            exact .call cursor)
    have called : ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block
        (.expr (.call context arguments origin) statementOrigin :: later)
        (@ReachableScalarCallCursor cfg env caller results loop) ∧
      ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block
        (.expr (.call context arguments origin) statementOrigin :: later) := ⟨accepted_generated_reachable_sequence_prefix_cons selected before loop bindings want block _ head suffix.1,
      accepted_generated_reachable_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_reachable_control_call_statement_stopped_family contextAt implAt depth callee form hasValue
          shrink stoppedArgumentsForm selected loop) suffix.2⟩
    exact accepted_generated_invariant_scalar_assignment_statements_prepend selected before loop bindings want block earlierForm
      (@ReachableScalarCallCursor cfg env caller results loop)
      (by intro statement state source before built initial start map required runtime cursor; exact .scalar cursor)
      (fun point => RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point.point point.frame point.state)
      (fun valid steps => steps.reachable valid) called

theorem ReachableScalarCallStatements.toMixed {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : ReachableScalarCallStatements cfg env statements) : ReachableMixedCallStatements cfg env statements := by
  induction form with
  | mixed fragment =>
    exact .mixed (by simpa using WhileMixedStatements.scalar fragment WhileMixedStatements.nil)
  | call earlierForm context arguments origin statementOrigin ctx impl contextAt implAt depth fragment expression exprForm hasValue shrink argumentsForm stoppedArgumentsForm tail ih =>
    exact .call (by simpa using WhileMixedStatements.scalar earlierForm WhileMixedStatements.nil)
      context arguments origin statementOrigin ctx impl contextAt implAt depth fragment expression exprForm hasValue shrink
      argumentsForm stoppedArgumentsForm ih

theorem ReachableScalarCallStatements.normal {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : ReachableScalarCallStatements cfg env statements) {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env statements state = .ok flow after) : flow = .normal .unit :=
  form.toMixed.normal done

#print axioms ReachableScalarCallStatements.normal

#print axioms accepted_generated_reachable_scalar_call_statements
end Goose.Lower
