import Goose.Lower.DemandCallSplitReadContext
import Goose.Lower.DemandLoadStopped

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_split_read_stop {cfg : Cfg} {env : Env} {initialState state : St}
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
    {taken : Nat} {runtime : DemandRuntimePoint} (unfinished : taken < 2)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel runtime stop after) (nonTimeout : stop ≠ .timeout) :
    evalArg 3 cfg env (.byVal (.read place)) state = .stop stop after := by
  obtain ⟨retained, occurrence, rows, _, _, childExtended⟩ :=
    accepted_generated_call_split_read_context source found child canonical occurrence rows coverage split realized extended
  let le := lowerEnv cfg.mod env.vars results
  let stage := (lowerArgs (arguments.take index) le before).2
  let addressed := lowerPlace place le stage
  obtain ⟨placeChild, typing, roots, metadata⟩ := child.readChild
  have placeOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root placeChild.path (.place place) stage := by
    rw [metadata.path]
    exact .first occurrence (.expressionPlace rfl)
  have placeRows : GeneratedDemandRows cfg.mod placeChild.rootsEnv.access placeOccurrence
      ⟨retained ++ required.values, required.runs⟩ := by
    have inherited := GeneratedDemandRows.first (first := .expressionPlace rfl) rows
    simpa only [roots, metadata.path] using inherited
  obtain ⟨location, placed, post, firstStep⟩ := accepted_generated_scalar_place_address placeChild form
    placeOccurrence placeRows input.atPoint input.related (generated_read_place_extended childExtended)
  let middle : DemandRuntimePoint := ⟨(start.1, start.2 + 1), initial.set addressed.1 (.val (.ref location)), state⟩
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨length, current, rfl, actual, tail⟩
  · exact (stopped.excludes_step_nonTimeout nonTimeout (firstStep targetFuel)).elim
  · obtain ⟨fuel, actualStep⟩ := runtimeStep_demandInstructionStep actual
    have same := actualStep.deterministic (firstStep fuel)
    have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
    subst current
    rcases tail.uncons with ⟨rfl, rfl⟩ | ⟨remaining, next, length, step, residual⟩
    · have done := accepted_generated_load_runtime_stop child occurrence rows placed post childExtended stopped nonTimeout
      simpa [evalArg, done]
    · omega

#print axioms accepted_generated_call_split_read_stop
end Goose.Lower
