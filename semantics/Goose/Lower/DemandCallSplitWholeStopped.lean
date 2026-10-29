import Goose.Lower.DemandCallSplitMixedFrontier
import Goose.Lower.DemandCallWholeCommon
import Goose.Lower.DemandCallSliceMixedOutcome

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_split_call_stopped_expression {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {caller : Func} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
      source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (shrink : cfg.mod.profile = .shrink) (form : SplitMixedArguments source.rootsEnv.access arguments)
    (agreement : GeneratedCallFrontierAgreement source caller results before initial map)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    StoppedExpressionPrefix source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before initial start taken reached stop after := by
  have progress := accepted_generated_call_split_mixed_stopped source occurrence rows coverage admitted bounded
    realized input extended shrink form steps stopped nonTimeout
  have shared : StoppedCallArgumentsProgress source caller results before initial start taken reached stop after := by
    cases progress with
    | aborted trace => exact .aborted trace
    | @complete consumed remaining boundary values prior slots count executed residual trace tracked argumentBounded argumentRealized checked post cells argumentInput =>
      exact .complete count executed residual trace (by simpa using post) (by simpa using cells)
  exact accepted_generated_call_stopped_from_frontier source extended agreement callerStart stopped nonTimeout shared


theorem accepted_generated_slice_split_unit_call_stopped_expression {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl) (depth : env.depth < maxCallDepth)
    (fragment : ∀ middle : St, SliceMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    {caller : Func} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop
      source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (shrink : cfg.mod.profile = .shrink) (form : SplitMixedArguments source.rootsEnv.access arguments)
    (callerStart : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    StoppedExpressionPrefix source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before initial start taken reached stop after := by
  have agreement : GeneratedCallFrontierAgreement source caller results before initial map := by
    constructor
    · intro argumentFuel targetFuel values middle after frame point stop argumentsDone callPost read callerPoint execution nonTimeout
      exact accepted_generated_actual_slice_mixed_unit_call_instruction_stop source argumentsDone contextAt implAt depth (fragment middle) noResults noValue
        callPost read callerPoint extended execution nonTimeout
    · intro argumentFuel targetFuel values middle after frame point value argumentsDone callPost read callerPoint execution
      obtain ⟨valueEq, built, sourceFuel, evaluated, builtEq, step, boundary⟩ :=
        accepted_generated_actual_slice_mixed_unit_call_success source argumentsDone contextAt implAt depth (fragment middle) noResults noValue
          callPost read callerPoint extended admitted bounded realized execution
      subst built
      exact ⟨sourceFuel, evaluated, boundary⟩
  exact accepted_generated_split_call_stopped_expression source occurrence rows coverage admitted bounded realized input extended
    shrink form agreement callerStart steps stopped nonTimeout


#print axioms accepted_generated_slice_split_unit_call_stopped_expression

#print axioms accepted_generated_split_call_stopped_expression
end Goose.Lower
