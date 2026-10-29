import Goose.Lower.DemandCallSplitMixedStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_split_mixed_stopped {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (shrink : cfg.mod.profile = .shrink) (form : SplitMixedArguments source.rootsEnv.access arguments)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {fuel : Nat} {stop : Stop} {after : St} (stopped : DemandInstructionStop cx fuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    CallSplitStoppedCells source cx results before loop map initial [] 0 arguments ⟨start, initial, state⟩ taken reached stop after := by
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
  have cells : CallArgumentCells (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).1 []
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).2.vals.size initial := by
    simpa [lowerArgs, pure_run] using CallArgumentCells.empty before.vals.size initial
  have wholePost : Post cfg env cx before initial
      (lowerArgs (arguments.take 0) (lowerEnv cfg.mod env.vars results) before).2 initial start [] := by
    simpa [lowerArgs, pure_run] using Post.init input.related input.atPoint
  exact accepted_generated_call_split_mixed_stop source occurrence rows form sources canonical admitted coverage shrink split
    wholePost cells input' bounded' realized' (by simp) extended steps stopped nonTimeout

theorem CallSplitStoppedCells.frontier {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    {source : ExprSource cfg env (.call context arguments origin) state}
    {cx : FnCtx} {results : List Ty} {before : LS} {loop : Option LoopCtx} {map : RetainedSsaMap}
    {initial : GIR.Frame} {start : Pt} {taken : Nat} {reached : DemandRuntimePoint} {stop : Stop} {after : St}
    (outcome : CallSplitStoppedCells source cx results before loop map initial [] 0 arguments ⟨start, initial, state⟩ taken reached stop after)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    (∃ fuel, mapList (evalArg fuel cfg env) arguments state = .stop stop after) ∨
    ∃ (sourceFuel consumed remaining : Nat) (boundary : DemandRuntimePoint) (values : List Val),
      consumed + remaining = taken ∧
      DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ boundary ∧
      DemandRuntimePrefix cx remaining boundary reached ∧
      mapList (evalArg sourceFuel cfg env) arguments state = .ok values boundary.state ∧
      mapList (getVal boundary.frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 boundary.state =
        .ok values boundary.state ∧
      instAt cx.fn boundary.point = some (.def (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1
        (.call context (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 (some origin))) := by
  cases outcome with
  | aborted trace => exact Or.inl trace.fuel.2
  | @complete consumed remaining boundary values prior slots count executed residual trace tracked bounded realized checked wholePost cells input =>
    obtain ⟨sourceFuel, evaluated⟩ := trace.fuel
    have read := cells.read boundary.state
    have point : (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2.pp = some boundary.point := by
      simpa using input.atPoint
    let le := lowerEnv cfg.mod env.vars results
    obtain ⟨ids, middle, afterCall, argsRun, definition, tail⟩ := lowerExpr_call_split
      (show lowerExpr (.call context arguments origin) le before =
        ((lowerExpr (.call context arguments origin) le before).1, (lowerExpr (.call context arguments origin) le before).2) from rfl)
    have afterExtended : ExtT afterCall cx.fn.blocks := by
      rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
      · exact extended.of_adv (adv_emitTerm term)
      · exact extended
    have sameIds : ids = (lowerArgs arguments le before).1 := by rw [argsRun]
    have sameMiddle : middle = (lowerArgs arguments le before).2 := by rw [argsRun]
    subst ids
    subst middle
    have instruction := (emitDef_facts definition point afterExtended).2.2.2.2
    exact Or.inr ⟨sourceFuel, consumed, remaining, boundary, values, count, executed, residual, evaluated,
      by simpa using read, instruction⟩

#print axioms CallSplitStoppedCells.frontier
#print axioms accepted_generated_call_split_mixed_stopped
end Goose.Lower
