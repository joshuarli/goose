import Goose.Lower.DemandCallSplitReadContext

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_split_read_next {cfg : Cfg} {env : Env} {initialState state : St}
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
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime) :
    ∃ (retained : List (ValueId × RetainedAlias)) (label : DemandSourceLabel) (id : ValueId) (operation : Op),
      GeneratedDemandInstruction cfg.mod child.rootsEnv.access cx.fn ⟨retained ++ required.values, required.runs⟩
        label runtime.point (.def id operation) ∧
      (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Covers
        ⟨retained ++ required.values, required.runs⟩ ∧
      SplitRequiredOperandsAt ⟨retained ++ required.values, required.runs⟩ cfg.mod source.world env
        ⟨start, initial, state⟩ := by
  obtain ⟨retained, childOccurrence, childRows, splitCoverage, requiredRealized, childExtended⟩ :=
    accepted_generated_call_split_read_context source found child canonical occurrence rows coverage split realized extended
  obtain ⟨label, id, operation, site⟩ := accepted_generated_scalar_read_next child form childOccurrence childRows
    input.atPoint input.related childExtended unfinished steps
  exact ⟨retained, label, id, operation, site, splitCoverage, requiredRealized⟩

#print axioms accepted_generated_call_split_read_next
end Goose.Lower
