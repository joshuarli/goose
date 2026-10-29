import Goose.Lower.DemandCallSplitReadContext
import Goose.Lower.DemandCallSplitValueBoundary
import Goose.Lower.DemandScalarReadCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_split_read_complete {cfg : Cfg} {env : Env} {initialState state : St}
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
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)

    {runtime : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx 2 ⟨start, initial, state⟩ runtime) :
    ∃ value, evalExpr 2 cfg env (.read place) state = .ok value runtime.state ∧
      GeneratedExpressionPrefixEnd child ⟨values ++ map.values, map.runs⟩ cx
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial
        (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2
        (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1 value runtime := by
  obtain ⟨retained, occurrence, rows, coverage, requiredRealized, childExtended⟩ :=
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
  have childRealized : (⟨values ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod child.world env ⟨start, initial, state⟩ := by
    simpa only [canonical.2.2.1] using realized.1
  have carried := childRealized.retained post.same bounded.1.1 bounded.1.2 RetainsAliases.refl
  rcases steps.uncons with ⟨impossible, _⟩ | ⟨remaining, current, length, actual, tail⟩
  · omega
  obtain ⟨fuel, actualStep⟩ := runtimeStep_demandInstructionStep actual
  have same := actualStep.deterministic (firstStep fuel)
  have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
  subst current
  rcases tail.uncons with ⟨impossible, _⟩ | ⟨remaining, final, lengthTail, loaded, residual⟩
  · omega
  have residualZero : remaining = 0 := by omega
  subst remaining
  rcases residual.uncons with ⟨_, rfl⟩ | ⟨rest, _, impossible, _, _⟩ <;> try omega
  obtain ⟨_, _, _, value, _, _, evaluated, finalPost, _, _⟩ :=
    accepted_generated_load_runtime_step_independent child occurrence rows placed post (bounded.1.mono post.mono) carried childExtended loaded
  have childAdmission := (SplitCallRetained.byValAdmission source found child canonical admitted split).1
  exact ⟨value, evaluated, ExpressionDemandBoundary.of_result (child.result 2 value evaluated) childAdmission bounded.1 childRealized finalPost⟩

theorem accepted_generated_call_split_read_finish {cfg : Cfg} {env : Env} {initialState state : St}
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
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)

    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasArg (source.path ++ [index]) (.byVal (.read place)) = .ok aliases)
    (checked : ∀ cell ∈ slots, cell.Checked source index initial)
    {runtime : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx 2 ⟨start, initial, state⟩ runtime) :
    ∃ value,
      evalArg 3 cfg env (.byVal (.read place)) state = .ok value runtime.state ∧
      let id := (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1
      let nextValues := values ++ aliases.map (fun alias => (id, alias))
      SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1))
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).1 nextValues slots ∧
      (⟨⟨nextValues ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes cfg.mod source.world env runtime ∧
      (⟨⟨nextValues ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      (∀ cell ∈ slots, cell.Checked source (index + 1) runtime.frame) ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 runtime.frame runtime.point := by
  obtain ⟨value, evaluated, boundary⟩ := accepted_generated_call_split_read_complete source found child form canonical
    occurrence rows coverage split realized admitted bounded input extended steps
  obtain ⟨nextRows, nextRealized, nextBounded, nextChecked⟩ :=
    accepted_generated_call_split_value_finish (cx := cx) (results := results) (map := map)
      source found child canonical split query boundary checked bounded.2
  have nextInput := accepted_generated_call_value_next_input (map := ⟨values ++ map.values, map.runs⟩)
    source found child input boundary
  exact ⟨value, by simpa [evalArg, evaluated], nextRows, nextRealized, nextBounded, nextChecked, nextInput⟩

#print axioms accepted_generated_call_split_read_finish

#print axioms accepted_generated_call_split_read_complete
end Goose.Lower
