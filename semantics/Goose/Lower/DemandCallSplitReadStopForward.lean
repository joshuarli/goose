import Goose.Lower.DemandCallSplitReadContext
import Goose.Lower.DemandScalarReadStopForward
import Goose.Lower.DemandScalarReadFuel

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_split_read_stop_forward {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {place : Place} (found : arguments[index]? = some (.byVal (.read place)))
    (child : ExprSource cfg env (.read place) state) (form : ScalarReadPlace place)
    (canonical : (ArgSource.byVal child).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byVal (.read place)) found))
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell}
    (split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 values slots)
    {initial : GIR.Frame} {start : Pt}
    (realized : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes
      cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {fuel : Nat} {stop : Stop} {after : St}
    (evaluated : evalArg fuel cfg env (.byVal (.read place)) state = .stop stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ middle, DemandRuntimePrefix cx 1 ⟨start, initial, state⟩ middle ∧
      DemandInstructionStop cx 1 middle stop after := by
  obtain ⟨retained, childOccurrence, childRows, _, _, childExtended⟩ :=
    accepted_generated_call_split_read_context source found child canonical occurrence rows coverage split realized extended
  have done : evalExpr 2 cfg env (.read place) state = .stop stop after := by
    simpa [evalArg] using scalar_read_argument_stop_fuel form evaluated nonTimeout
  exact accepted_generated_scalar_read_stop_forward child form childOccurrence childRows input.atPoint input.related childExtended done

#print axioms accepted_generated_call_split_read_stop_forward
end Goose.Lower
