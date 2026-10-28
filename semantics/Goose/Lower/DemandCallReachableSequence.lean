import Goose.Lower.DemandCallReachableStatement
import Goose.Lower.DemandReachableSequence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

inductive ReachableCallStatementFamilyCursor {cfg : Cfg} {env : Env} (caller : Func) (results : List Ty) (loop : Option LoopCtx) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | call {state : St} {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
      {source : StmtSource cfg env (.expr (.call context arguments origin) statementOrigin) state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ReachableCallStatementCursor source caller results before loop map initial start runtime) :
      ReachableCallStatementFamilyCursor caller results loop source before built initial start map required runtime

theorem ReachableCallStatementFamilyCursor.realizes {cfg : Cfg} {env : Env} {statement : Stmt} {state : St}
    {source : StmtSource cfg env statement state} {caller : Func} {results : List Ty} {loop : Option LoopCtx}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : ReachableCallStatementFamilyCursor caller results loop source before built initial start map required runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  cases cursor with
  | call cursor => exact cursor.realizes

theorem ReachableCallStatementFamilyCursor.progress {cfg : Cfg} {env : Env} {statement : Stmt} {state : St}
    {source : StmtSource cfg env statement state} {caller : Func} {results : List Ty} {loop : Option LoopCtx}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : ReachableCallStatementFamilyCursor caller results loop source before built initial start map required runtime) :
    (∃ id op, instAt caller runtime.point = some (.def id op)) ∨
      ∃ next, ∀ fuel, DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next := by
  cases cursor with
  | call cursor => exact cursor.progress

#print axioms ReachableCallStatementFamilyCursor.realizes
#print axioms ReachableCallStatementFamilyCursor.progress

theorem accepted_generated_reachable_control_call_statement_family {cfg : Cfg} {env : Env}
    {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl) (depth : env.depth < maxCallDepth)
    (fragment : ∀ middle : St, WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : impl.body.value = some expression)
    (shrink : cfg.mod.profile = .shrink)
    (argumentsForm : ∀ {state : St} (source : StmtSource cfg env (.expr (.call context arguments origin) statementOrigin) state),
      CallMixedArguments source.rootsEnv.access arguments)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner) (loop : Option LoopCtx) :
    ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop
      (.expr (.call context arguments origin) statementOrigin) (@ReachableCallStatementFamilyCursor cfg env caller results loop) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended callerStart taken reached steps
  have progress := accepted_generated_reachable_control_call_statement source contextAt implAt depth fragment form hasValue
    selected owned occurrence rows coverage admitted bounded realized input extended shrink (argumentsForm source) callerStart steps
  refine ⟨progress.sourceOwner, progress.coverage, ?_⟩
  cases progress.progress with
  | interior cursor => exact .interior (.call cursor)
  | complete count executed residual evaluated result => exact .complete count executed residual evaluated result

theorem accepted_generated_reachable_control_call_statement_stopped_family {cfg : Cfg} {env : Env}
    {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl) (depth : env.depth < maxCallDepth)
    (fragment : ∀ middle : St, WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : impl.body.value = some expression)
    (shrink : cfg.mod.profile = .shrink)
    (argumentsForm : ∀ {state : St} (source : StmtSource cfg env (.expr (.call context arguments origin) statementOrigin) state),
      CallMixedStoppedArguments source.rootsEnv.access arguments)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner) (loop : Option LoopCtx) :
    ReachableStoppedStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop
      (.expr (.call context arguments origin) statementOrigin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended callerStart taken reached steps targetFuel stop after stopped nonTimeout
  exact accepted_generated_reachable_control_call_statement_stopped source contextAt implAt depth fragment form hasValue
    selected owned occurrence rows coverage admitted bounded realized input extended shrink (argumentsForm source) callerStart steps stopped nonTimeout

inductive ReachableWhileCallStatementCursor {cfg : Cfg} {env : Env} (caller : Func) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | existing {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : WhileMixedStatementCursor ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected source before built initial start map required runtime) :
      ReachableWhileCallStatementCursor caller results selected source before built initial start map required runtime
  | call {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ReachableCallStatementFamilyCursor caller results none source before built initial start map required runtime) :
      ReachableWhileCallStatementCursor caller results selected source before built initial start map required runtime

theorem accepted_generated_reachable_control_call_while_tail {cfg : Cfg} {env : Env}
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
    (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {rest : List Stmt} (tail : WhileMixedStatements cfg env rest) :
    ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block
      (.expr (.call context arguments origin) statementOrigin :: rest)
      (@ReachableWhileCallStatementCursor cfg env caller results root owner selected) ∧
    ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block
      (.expr (.call context arguments origin) statementOrigin :: rest) := by
  have tailFamilies := accepted_generated_while_mixed_statements tail (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩)
    (results := results) selected before bindings want block
  have mappedTail : GeneratedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before none bindings want block rest
      (@ReachableWhileCallStatementCursor cfg env caller results root owner selected) :=
    GeneratedSequencePrefixFamily.mapCursor
      (cursor := @WhileMixedStatementCursor cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results root owner selected)
      (next := @ReachableWhileCallStatementCursor cfg env caller results root owner selected)
      (selected := selected) (before := before) (loop := none) (bindings := bindings) (want := want) (block := block) (statements := rest)
      (fun {state} => tailFamilies.1 (state := state)) (by
    intro statement state source before built initial start map required runtime cursor
    exact ReachableWhileCallStatementCursor.existing cursor)
  have head : ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected none
      (.expr (.call context arguments origin) statementOrigin)
      (@ReachableWhileCallStatementCursor cfg env caller results root owner selected) :=
    ReachableStatementPrefixFamily.mapCursor
      (cursor := @ReachableCallStatementFamilyCursor cfg env caller results none)
      (next := @ReachableWhileCallStatementCursor cfg env caller results root owner selected)
      (selected := selected) (loop := none) (statement := .expr (.call context arguments origin) statementOrigin)
      (accepted_generated_reachable_control_call_statement_family contextAt implAt depth fragment form hasValue
        shrink argumentsForm selected none) (by
      intro statement state source before built initial start map required runtime cursor
      exact ReachableWhileCallStatementCursor.call cursor)
  exact ⟨accepted_generated_reachable_sequence_prefix_cons selected before none bindings want block _ head mappedTail.reachable,
    accepted_generated_reachable_stopped_sequence_cons selected before none bindings want block
      (accepted_generated_reachable_control_call_statement_stopped_family contextAt implAt depth fragment form hasValue
        shrink stoppedArgumentsForm selected none)
      (GeneratedStoppedSequencePrefixFamily.reachable (selected := selected) (before := before) (loop := none)
        (bindings := bindings) (want := want) (block := block) (statements := rest)
        (fun {state} => tailFamilies.2 (state := state)))⟩

#print axioms accepted_generated_reachable_control_call_while_tail

theorem accepted_generated_reachable_control_call_sequence_cons {cfg : Cfg} {env : Env}
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
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {rest : List Stmt}
    (tail : ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block rest
      (@ReachableCallStatementFamilyCursor cfg env caller results loop))
    (tailStopped : ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block rest) :
    ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block
      (.expr (.call context arguments origin) statementOrigin :: rest) (@ReachableCallStatementFamilyCursor cfg env caller results loop) ∧
    ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block
      (.expr (.call context arguments origin) statementOrigin :: rest) := by
  constructor
  · exact accepted_generated_reachable_sequence_prefix_cons selected before loop bindings want block _
      (accepted_generated_reachable_control_call_statement_family contextAt implAt depth fragment form hasValue shrink argumentsForm selected loop) tail
  · exact accepted_generated_reachable_stopped_sequence_cons selected before loop bindings want block
      (accepted_generated_reachable_control_call_statement_stopped_family contextAt implAt depth fragment form hasValue shrink stoppedArgumentsForm selected loop) tailStopped

theorem accepted_generated_reachable_control_call_single {cfg : Cfg} {env : Env}
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
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block) :
    ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block
      [.expr (.call context arguments origin) statementOrigin] (@ReachableCallStatementFamilyCursor cfg env caller results loop) ∧
    ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block
      [.expr (.call context arguments origin) statementOrigin] := by
  apply accepted_generated_reachable_control_call_sequence_cons contextAt implAt depth fragment form hasValue shrink
    argumentsForm stoppedArgumentsForm selected before loop bindings want block
  · exact GeneratedSequencePrefixFamily.reachable (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩)
      (selected := selected) (before := before) (loop := loop) (bindings := bindings) (want := want) (block := block) (statements := [])
      (cursor := @ReachableCallStatementFamilyCursor cfg env caller results loop)
      (fun {state} => accepted_generated_sequence_prefix_nil selected before loop bindings want block _ (state := state))
  · exact GeneratedStoppedSequencePrefixFamily.reachable (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩)
      (selected := selected) (before := before) (loop := loop) (bindings := bindings) (want := want) (block := block) (statements := [])
      (fun {state} => accepted_generated_stopped_sequence_nil selected before loop bindings want block (state := state))

#print axioms accepted_generated_reachable_control_call_single

#print axioms accepted_generated_reachable_control_call_sequence_cons

#print axioms accepted_generated_reachable_control_call_statement_family
#print axioms accepted_generated_reachable_control_call_statement_stopped_family
end Goose.Lower
