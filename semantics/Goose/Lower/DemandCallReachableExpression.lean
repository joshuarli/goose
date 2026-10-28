import Goose.Lower.DemandCallControlWholePrefix
import Goose.Lower.DemandCallControlWholeStopped

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

inductive ReachableCallExpressionCursor {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    (caller : Func) (results : List Ty) (before : LS) (loop : Option LoopCtx) (map : RetainedSsaMap)
    (initial : GIR.Frame) (start : Pt) (runtime : DemandRuntimePoint) : Prop
  | arguments {required : RetainedSsaMap} {taken : Nat}
      (cursor : CallMixedPrefix source ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before loop map required
        0 arguments ⟨start, initial, state⟩ taken runtime)
      (realized : map.Realizes cfg.mod source.world env runtime)
      (progress : (∃ id op, instAt caller runtime.point = some (.def id op)) ∨
        ∃ next, ∀ fuel, DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next)
      (reachable : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller runtime.point runtime.frame runtime.state) :
      ReachableCallExpressionCursor source caller results before loop map initial start runtime
  | ready {fuel : Nat} {values : List Val}
      (evaluated : mapList (evalArg fuel cfg env) arguments state = .ok values runtime.state)
      (realized : map.Realizes cfg.mod source.world env runtime)
      (post : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
        (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 runtime.frame runtime.point [])
      (read : mapList (getVal runtime.frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 runtime.state =
        .ok values runtime.state)
      (instruction : instAt caller runtime.point = some (.def
        (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1
        (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin))))
      (reachable : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller runtime.point runtime.frame runtime.state) :
      ReachableCallExpressionCursor source caller results before loop map initial start runtime

theorem accepted_generated_reachable_control_call_expression {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl) (depth : env.depth < maxCallDepth)
    (fragment : ∀ middle : St, WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : impl.body.value = some expression)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
      source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (shrink : cfg.mod.profile = .shrink) (argumentsForm : CallMixedArguments source.rootsEnv.access arguments)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached) :
    GeneratedExpressionPrefixDecomposition (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) (results := results)
      source selected occurrence rows map initial start
      (ReachableCallExpressionCursor source caller results before loop map initial start) taken reached := by
  have cursor := accepted_generated_control_call_prefix source contextAt implAt depth fragment form hasValue selected owned occurrence rows
    coverage admitted bounded realized input extended shrink argumentsForm callerStart steps
  refine ⟨owned, coverage, ?_⟩
  cases cursor with
  | arguments cursor current progress => exact .interior (.arguments cursor current progress (steps.reachable callerStart))
  | ready evaluated current post read instruction => exact .interior (.ready evaluated current post read instruction (steps.reachable callerStart))
  | complete count executed residual evaluated result => exact .complete count executed residual evaluated result

theorem ReachableCallExpressionCursor.realizes {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    {source : ExprSource cfg env (.call context arguments origin) state}
    {caller : Func} {results : List Ty} {before : LS} {loop : Option LoopCtx} {map : RetainedSsaMap}
    {initial : GIR.Frame} {start : Pt} {runtime : DemandRuntimePoint}
    (cursor : ReachableCallExpressionCursor source caller results before loop map initial start runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  cases cursor with
  | arguments _ realized _ _ => exact realized
  | ready _ realized _ _ _ _ => exact realized

theorem ReachableCallExpressionCursor.progress {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    {source : ExprSource cfg env (.call context arguments origin) state}
    {caller : Func} {results : List Ty} {before : LS} {loop : Option LoopCtx} {map : RetainedSsaMap}
    {initial : GIR.Frame} {start : Pt} {runtime : DemandRuntimePoint}
    (cursor : ReachableCallExpressionCursor source caller results before loop map initial start runtime) :
    (∃ id op, instAt caller runtime.point = some (.def id op)) ∨
      ∃ next, ∀ fuel, DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next := by
  cases cursor with
  | arguments _ _ progress _ => exact progress
  | ready _ _ _ _ instruction _ => exact .inl ⟨_, _, instruction⟩

#print axioms ReachableCallExpressionCursor.realizes
#print axioms ReachableCallExpressionCursor.progress

#print axioms accepted_generated_reachable_control_call_expression
end Goose.Lower
