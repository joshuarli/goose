import Goose.Lower.DemandCallSplitMixedArgumentsStopForward
import Goose.Lower.DemandStoppedForward

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_call_split_mixed_arguments_runAt_stop {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (form : SplitMixedArguments source.rootsEnv.access arguments) {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (coverage : map.Covers required) (shrink : cfg.mod.profile = .shrink)
    {sourceFuel : Nat} {stop : Stop} {after : St}
    (sourceStop : mapList (evalArg sourceFuel cfg env) arguments state = .stop stop after)
    (nonTimeout : stop ≠ .timeout)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ targetFuel, GIR.runAt cx start initial targetFuel state = .stop stop after := by
  obtain ⟨length, targetFuel, runtime, steps, stopped⟩ :=
    accepted_generated_call_split_mixed_arguments_stop_forward source occurrence rows form input admitted bounded realized
      coverage shrink sourceStop nonTimeout extended
  exact steps.runAt_stop stopped nonTimeout

#print axioms accepted_generated_call_split_mixed_arguments_runAt_stop
end Goose.Lower
