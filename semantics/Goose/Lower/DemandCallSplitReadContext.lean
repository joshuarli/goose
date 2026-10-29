import Goose.Lower.DemandCallSplitCoverage
import Goose.Lower.DemandScalarReadNext

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_split_read_context {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {place : Place} (found : arguments[index]? = some (.byVal (.read place)))
    (child : ExprSource cfg env (.read place) state)
    (canonical : (ArgSource.byVal child).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byVal (.read place)) found))
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell}
    (split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 values slots)
    {initial : GIR.Frame} {start : Pt}
    (realized : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes
      cfg.mod source.world env ⟨start, initial, state⟩)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    : ∃ (retained : List (ValueId × RetainedAlias))
      (childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root child.path (.expression (.read place)) (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2),
      GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence ⟨retained ++ required.values, required.runs⟩ ∧
      (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Covers ⟨retained ++ required.values, required.runs⟩ ∧
      SplitRequiredOperandsAt ⟨retained ++ required.values, required.runs⟩ cfg.mod source.world env ⟨start, initial, state⟩ ∧
      ExtT (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2 cx.fn.blocks := by
  have childAt := ArgSource.byVal_callChild source found child canonical
  obtain ⟨typing, roots⟩ := ArgSource.byVal_callMetadata source found child canonical
  obtain ⟨retained, argumentRows, splitCoverage⟩ := SplitCallRetained.argumentCoverage (argumentAt := found) rows coverage split
  let le := lowerEnv cfg.mod env.vars results
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.expression (.read place))
      (lowerArgs (arguments.take index) le before).2 := by
    rw [childAt.path]
    exact .argumentValue (.argument occurrence found)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence
      ⟨retained ++ required.values, required.runs⟩ := by
    have inherited := GeneratedDemandRows.argumentValue (expression := .read place) argumentRows
    simpa only [roots, childAt.path] using inherited
  obtain ⟨ids, middle, after, argsRun, definition, tail⟩ := lowerExpr_call_split
    (show lowerExpr (.call context arguments origin) le before =
      ((lowerExpr (.call context arguments origin) le before).1, (lowerExpr (.call context arguments origin) le before).2) from rfl)
  have afterExtended : ExtT after cx.fn.blocks := by
    rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
    · exact extended.of_adv (adv_emitTerm term)
    · exact extended
  have argsExtended : ExtT (lowerArgs arguments le before).2 cx.fn.blocks := by
    rw [argsRun]
    exact afterExtended.of_adv (adv_emitDef definition)
  obtain ⟨earlier, later, argsSplit, length, _, _, advance⟩ := lowerArgs_argument_checkpoint found le before
  have earlierEq : arguments.take index = earlier := by
    rw [argsSplit, ← length]
    simp
  have childExtended : ExtT (lowerExpr (.read place) le (lowerArgs (arguments.take index) le before).2).2 cx.fn.blocks := by
    rw [earlierEq]
    exact argsExtended.of_adv (by simpa [lowerArg] using advance)
  exact ⟨retained, childOccurrence, childRows, splitCoverage, splitCoverage.realizes realized, childExtended⟩

#print axioms accepted_generated_call_split_read_context
end Goose.Lower
