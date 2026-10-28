import Goose.Lower.DemandCallFirstArgument
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsCheckpoints

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_value_stage {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {expression : Expr} (found : arguments[index]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byVal expression) found))
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {prior : List (ValueId × RetainedAlias)}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {initial : GIR.Frame} {start : Pt}
    (bounded : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (form : ControlPrefixExpression expression)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    DemandPrefixDecomposition cx (fun fuel => evalExpr fuel cfg env expression)
      (GeneratedControlProgressCursor cx child
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2
        (lowerExpr expression (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2 initial start
        ⟨prior ++ map.values, map.runs⟩ ⟨prior ++ required.values, required.runs⟩)
      (GeneratedExpressionPrefixEnd child ⟨prior ++ map.values, map.runs⟩ cx
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial
        (lowerExpr expression (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2
        (lowerExpr expression (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1)
      taken ⟨start, initial, state⟩ reached := by
  have childAt := ArgSource.byVal_callChild source found child canonical
  obtain ⟨typing, roots⟩ := ArgSource.byVal_callMetadata source found child canonical
  have childOwner : GeneratedSourceOwner selected child.context :=
    (owned.child rfl index (.expression expression) .expression
      (by simp [DemandNode.child?, DemandNode.children, found]) (by trivial)).transport
        childAt.plans.symm childAt.path.symm rfl childAt.context.symm
  have argumentOccurrence := GeneratedDemandOccurrence.argument occurrence found
  have argumentRows := GeneratedDemandRows.argument rows (argumentAt := found) tracked
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.expression expression)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 := by
    rw [childAt.path]
    exact .argumentValue argumentOccurrence
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence
      ⟨prior ++ required.values, required.runs⟩ := by
    have inherited := GeneratedDemandRows.argumentValue argumentRows
    simpa only [roots, childAt.path] using inherited
  have childCoverage : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Covers ⟨prior ++ required.values, required.runs⟩ := by
    constructor
    · intro cell member
      rcases List.mem_append.mp member with priorMember | inherited
      · exact List.mem_append_left _ priorMember
      · exact List.mem_append_right _ (coverage.1 cell inherited)
    · exact coverage.2
  have childAdmitted : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Admitted cfg.mod.profile child.context.retained := by
    intro profile alias member
    simp only [RetainedSsaMap.values, RetainedSsaMap.runs, List.map_append, List.mem_append] at member
    rcases member with (priorMember | inherited) | inherited
    · obtain ⟨cell, cellMember, same⟩ := List.mem_map.mp priorMember
      rw [← same]
      exact ArgSource.byVal_callRetainsPrior source found child canonical tracked profile cell cellMember
    · exact childAt.retained alias (admitted profile alias (List.mem_append_left _ inherited))
    · exact childAt.retained alias (admitted profile alias (List.mem_append_right _ inherited))
  have childRealized : (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod child.world env ⟨start, initial, state⟩ := by
    simpa only [childAt.world] using realized
  have childInput : GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start := by
    simpa only [typing, roots] using input
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨ids, middle, after, argsRun, definition, tail⟩ := lowerExpr_call_split
    (show lowerExpr (.call context arguments origin) le before =
      ((lowerExpr (.call context arguments origin) le before).1, (lowerExpr (.call context arguments origin) le before).2) from rfl)
  have afterExtended : ExtT after cx.fn.blocks := by
    rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
    · exact extended.of_adv (adv_emitTerm term)
    · exact extended
  have middleExtended := afterExtended.of_adv (adv_emitDef definition)
  have argsExtended : ExtT (lowerArgs arguments le before).2 cx.fn.blocks := by
    rw [argsRun]
    exact middleExtended
  obtain ⟨earlier, later, split, length, _, _, advance⟩ := lowerArgs_argument_checkpoint found le before
  have earlierEq : arguments.take index = earlier := by
    rw [split, ← length]
    simp
  have childExtended : ExtT (lowerExpr expression le (lowerArgs (arguments.take index) le before).2).2 cx.fn.blocks := by
    rw [earlierEq]
    exact argsExtended.of_adv (by simpa [lowerArg] using advance)
  have family : GeneratedExpressionPrefixFamily cx results selected loop expression
      (@GeneratedControlProgressCursor cfg env cx) := accepted_generated_control_progress_prefix_family selected loop form
  exact (family child childOwner childOccurrence childRows childCoverage childAdmitted bounded childRealized childInput childExtended steps).progress

#print axioms accepted_generated_call_value_stage
end Goose.Lower
