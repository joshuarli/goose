import Goose.Lower.DemandCallSplitMixedStopForward

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_split_mixed_arguments_stop_forward {cfg : Cfg} {env : Env} {state : St}
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
    ∃ (length targetFuel : Nat) (runtime : DemandRuntimePoint),
      DemandRuntimePrefix cx length ⟨start, initial, state⟩ runtime ∧
      DemandInstructionStop cx targetFuel runtime stop after := by
  let sources := fun fuel => Classical.choose (source.callArgsCanonical fuel results input.metadata)
  have canonical : ∀ fuel, (sources fuel).CallChildren source 0 := by
    intro fuel
    exact (Classical.choose_spec (source.callArgsCanonical fuel results input.metadata)).2
  have split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take 0)
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).1 [] [] := by
    simpa [lowerArgs, pure_run] using (SplitCallArgumentRows.nil (access := source.rootsEnv.access) (path := source.path) 0)
  have input' : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).2 initial start := by
    simpa [lowerArgs, pure_run] using input
  have bounded' : (⟨⟨[] ++ map.values, map.runs⟩, []⟩ : SplitCallRetained).Bounded
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).2.vals.size := by
    simpa [SplitCallRetained.Bounded, lowerArgs, pure_run] using bounded
  have realized' : (⟨⟨[] ++ map.values, map.runs⟩, []⟩ : SplitCallRetained).Realizes
      cfg.mod source.world env ⟨start, initial, state⟩ := by
    exact ⟨by simpa using realized, by simp [SliceSlotArgumentCells.Realizes]⟩
  exact accepted_generated_call_split_mixed_stop_forward source occurrence rows form sources canonical admitted coverage shrink
    (CallArgumentsStopped.of_mapList sourceStop nonTimeout) nonTimeout split input' bounded' realized' (by simp) extended

#print axioms accepted_generated_call_split_mixed_arguments_stop_forward
end Goose.Lower
