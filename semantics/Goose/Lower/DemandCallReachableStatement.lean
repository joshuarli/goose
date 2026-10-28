import Goose.Lower.DemandCallReachableExpression
import Goose.Lower.DemandStoppedStatementFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

inductive ReachableCallStatementCursor {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
    (source : StmtSource cfg env (.expr (.call context arguments origin) statementOrigin) state)
    (caller : Func) (results : List Ty) (before : LS) (loop : Option LoopCtx) (map : RetainedSsaMap)
    (initial : GIR.Frame) (start : Pt) (runtime : DemandRuntimePoint) : Prop
  | expression {child : ExprSource cfg env (.call context arguments origin) state}
      (canonical : source.ExpressionChildAt child rfl)
      (cursor : ReachableCallExpressionCursor child caller results before loop map initial start runtime) :
      ReachableCallStatementCursor source caller results before loop map initial start runtime

theorem accepted_generated_reachable_control_call_statement {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
    (source : StmtSource cfg env (.expr (.call context arguments origin) statementOrigin) state)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl) (depth : env.depth < maxCallDepth)
    (fragment : ∀ middle : St, WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : impl.body.value = some expression)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.expr (.call context arguments origin) statementOrigin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
      source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.expr (.call context arguments origin) statementOrigin)
      (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (shrink : cfg.mod.profile = .shrink) (argumentsForm : CallMixedArguments source.rootsEnv.access arguments)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached) :
    GeneratedStatementPrefixDecomposition (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) (results := results)
      source selected occurrence rows map initial start
      (ReachableCallStatementCursor source caller results before loop map initial start) taken reached := by
  obtain ⟨child, typing, roots, canonical, childOccurrence, childRows, childOwner, childAdmitted,
    childRealized, childInput, childExtended, lowered⟩ :=
    accepted_generated_expression_statement_entry source selected owned occurrence rows admitted realized input extended
  have childForm : CallMixedArguments child.rootsEnv.access arguments := by simpa only [roots] using argumentsForm
  have childProgress := accepted_generated_reachable_control_call_expression child contextAt implAt depth fragment form hasValue
    selected childOwner childOccurrence childRows coverage childAdmitted bounded childRealized childInput childExtended shrink childForm callerStart steps
  refine ⟨owned, coverage, ?_⟩
  cases childProgress.progress with
  | interior cursor => exact .interior (.expression canonical cursor)
  | @complete sourceFuel consumed remaining boundary value count prefixSteps residual evaluated finished =>
    have raw : execStmt (sourceFuel + 1) cfg env (.expr (.call context arguments origin) statementOrigin) state =
        .ok (.normal .unit) boundary.state := by
      simp only [execStmt, bind_apply, evaluated, pure_apply]
    have prepared : (execStmt (sourceFuel + 1) cfg env (.expr (.call context arguments origin) statementOrigin) >>= prepareLoopFlow env loop) state =
        .ok (.normal .unit) boundary.state := by
      simp only [bind_apply, raw]
      cases loop <;> rfl
    have carried : map.Realizes cfg.mod source.world env boundary := by
      simpa only [RetainedSsaMap.Realizes, canonical.world] using finished.demanded.operands
    exact .complete count prefixSteps residual prepared
      (.normal (by rw [lowered]; exact Post.nil finished.post.pp finished.post.mono finished.post.same finished.post.rel)
        (source.result (sourceFuel + 1) (.normal .unit) raw) (by rw [lowered]; exact finished.bounded) carried)

theorem accepted_generated_reachable_control_call_statement_stopped {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
    (source : StmtSource cfg env (.expr (.call context arguments origin) statementOrigin) state)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl) (depth : env.depth < maxCallDepth)
    (fragment : ∀ middle : St, WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : impl.body.value = some expression)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.expr (.call context arguments origin) statementOrigin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
      source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.expr (.call context arguments origin) statementOrigin)
      (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (shrink : cfg.mod.profile = .shrink) (argumentsForm : CallMixedStoppedArguments source.rootsEnv.access arguments)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    StoppedStatementPrefix source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop before initial start taken reached stop after := by
  obtain ⟨child, typing, roots, canonical, childOccurrence, childRows, childOwner, childAdmitted,
    childRealized, childInput, childExtended, lowered⟩ :=
    accepted_generated_expression_statement_entry source selected owned occurrence rows admitted realized input extended
  have childForm : CallMixedStoppedArguments child.rootsEnv.access arguments := by simpa only [roots] using argumentsForm
  have childProgress := accepted_generated_control_call_stopped_expression child contextAt implAt depth fragment form hasValue
    selected childOwner childOccurrence childRows coverage childAdmitted bounded childRealized childInput childExtended shrink childForm callerStart steps stopped nonTimeout
  cases childProgress with
  | aborted sourceFuel expressionStopped =>
    apply StoppedStatementPrefix.aborted (sourceFuel + 1)
    simp only [bind_apply, execStmt, expressionStopped]
  | @complete sourceFuel consumed remaining boundary value count prefixSteps residual evaluated finished =>
    have raw : execStmt (sourceFuel + 1) cfg env (.expr (.call context arguments origin) statementOrigin) state =
        .ok (.normal .unit) boundary.state := by
      simp only [execStmt, bind_apply, evaluated, pure_apply]
    have prepared : (execStmt (sourceFuel + 1) cfg env (.expr (.call context arguments origin) statementOrigin) >>= prepareLoopFlow env loop) state =
        .ok (.normal .unit) boundary.state := by
      simp only [bind_apply, raw]
      cases loop <;> rfl
    have carried : map.Realizes cfg.mod source.world env boundary := by
      simpa only [RetainedSsaMap.Realizes, canonical.world] using finished.demanded.operands
    exact .complete count prefixSteps residual prepared
      (.normal (by rw [lowered]; exact Post.nil finished.post.pp finished.post.mono finished.post.same finished.post.rel)
        (source.result (sourceFuel + 1) (.normal .unit) raw) (by rw [lowered]; exact finished.bounded) carried)

theorem ReachableCallStatementCursor.realizes {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
    {source : StmtSource cfg env (.expr (.call context arguments origin) statementOrigin) state}
    {caller : Func} {results : List Ty} {before : LS} {loop : Option LoopCtx} {map : RetainedSsaMap}
    {initial : GIR.Frame} {start : Pt} {runtime : DemandRuntimePoint}
    (cursor : ReachableCallStatementCursor source caller results before loop map initial start runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  cases cursor with
  | expression canonical cursor => simpa only [RetainedSsaMap.Realizes, canonical.world] using cursor.realizes

theorem ReachableCallStatementCursor.progress {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
    {source : StmtSource cfg env (.expr (.call context arguments origin) statementOrigin) state}
    {caller : Func} {results : List Ty} {before : LS} {loop : Option LoopCtx} {map : RetainedSsaMap}
    {initial : GIR.Frame} {start : Pt} {runtime : DemandRuntimePoint}
    (cursor : ReachableCallStatementCursor source caller results before loop map initial start runtime) :
    (∃ id op, instAt caller runtime.point = some (.def id op)) ∨
      ∃ next, ∀ fuel, DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next := by
  cases cursor with
  | expression canonical cursor => exact cursor.progress

#print axioms ReachableCallStatementCursor.realizes
#print axioms ReachableCallStatementCursor.progress

#print axioms accepted_generated_reachable_control_call_statement_stopped

#print axioms accepted_generated_reachable_control_call_statement
end Goose.Lower
