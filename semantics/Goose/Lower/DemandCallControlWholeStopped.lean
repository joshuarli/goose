import Goose.Lower.DemandCallWholeStopped
import Goose.Lower.DemandCallControlActualSuccess
import Goose.Lower.DemandCallControlInstructionStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_control_call_frontier_agreement {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl) (depth : env.depth < maxCallDepth)
    (fragment : ∀ middle : St, WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : impl.body.value = some expression)
    {caller : Func} {results : List Ty} {before : LS}
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    : GeneratedCallFrontierAgreement source caller results before initial map := by
  constructor
  · intro argumentFuel targetFuel values middle after frame point stop argumentsDone callPost read callerPoint execution nonTimeout
    exact accepted_generated_actual_control_call_instruction_stop source argumentsDone contextAt implAt depth (fragment middle) form hasValue
      callPost read callerPoint extended execution nonTimeout
  · intro argumentFuel targetFuel values middle after frame point value argumentsDone callPost read callerPoint execution
    obtain ⟨built, sourceFuel, evaluated, builtEq, step, boundary⟩ :=
      accepted_generated_actual_control_call_success source argumentsDone contextAt implAt depth (fragment middle) form hasValue
        callPost read callerPoint extended admitted bounded realized execution
    subst built
    exact ⟨sourceFuel, evaluated, boundary⟩


theorem accepted_generated_control_call_stopped_expression {cfg : Cfg} {env : Env} {state : St}
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
    (shrink : cfg.mod.profile = .shrink) (argumentsForm : CallMixedStoppedArguments source.rootsEnv.access arguments)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    StoppedExpressionPrefix source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before initial start taken reached stop after := by
  have agreement := accepted_generated_control_call_frontier_agreement source contextAt implAt depth fragment form hasValue
    admitted bounded realized extended
  exact accepted_generated_call_stopped_expression source selected owned occurrence rows coverage admitted bounded realized input extended
    shrink argumentsForm agreement callerStart steps stopped nonTimeout



#print axioms accepted_generated_control_call_frontier_agreement
#print axioms accepted_generated_control_call_stopped_expression
end Goose.Lower
