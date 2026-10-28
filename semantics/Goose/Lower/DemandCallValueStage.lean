import Goose.Lower.DemandCallFirstArgument
import Goose.Lower.DemandReadStoppedFamily
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsCheckpoints

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_value_stage_ready {cfg : Cfg} {env : Env} {initialState state : St}
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
    : ∃ childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root child.path (.expression expression)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2,
      GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence ⟨prior ++ required.values, required.runs⟩ ∧
      GeneratedSourceOwner selected child.context ∧
      (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Covers ⟨prior ++ required.values, required.runs⟩ ∧
      (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Admitted cfg.mod.profile child.context.retained ∧
      (⟨prior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod child.world env ⟨start, initial, state⟩ ∧
      GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start ∧
      ExtT (lowerExpr expression (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2 cx.fn.blocks := by
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
  exact ⟨childOccurrence, childRows, childOwner, childCoverage, childAdmitted, childRealized, childInput, childExtended⟩

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
  obtain ⟨childOccurrence, childRows, childOwner, childCoverage, childAdmitted, childRealized, childInput, childExtended⟩ :=
    accepted_generated_call_value_stage_ready source found child canonical selected owned occurrence rows tracked
      coverage admitted bounded realized input extended
  have family : GeneratedExpressionPrefixFamily cx results selected loop expression
      (@GeneratedControlProgressCursor cfg env cx) := accepted_generated_control_progress_prefix_family selected loop form
  exact (family child childOwner childOccurrence childRows childCoverage childAdmitted bounded childRealized childInput childExtended steps).progress

theorem accepted_generated_call_value_stage_stopped {cfg : Cfg} {env : Env} {initialState state : St}
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
    (form : ReadStoppedExpression expression)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {fuel : Nat} {stop : Stop} {after : St} (stopped : DemandInstructionStop cx fuel reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    StoppedExpressionPrefix child ⟨prior ++ map.values, map.runs⟩ cx results
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start taken reached stop after := by
  obtain ⟨childOccurrence, childRows, childOwner, childCoverage, childAdmitted, childRealized, childInput, childExtended⟩ :=
    accepted_generated_call_value_stage_ready source found child canonical selected owned occurrence rows tracked
      coverage admitted bounded realized input extended
  exact accepted_generated_read_stopped_expressions selected loop form child childOwner childOccurrence childRows
    childCoverage childAdmitted bounded childRealized childInput childExtended steps stopped nonTimeout

theorem accepted_generated_call_value_finish {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {expression : Expr} (found : arguments[index]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byVal expression) found))
    {cx : FnCtx} {results : List Ty} {before : LS} {initial : GIR.Frame} {map : RetainedSsaMap}
    {prior : List (ValueId × RetainedAlias)}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasArg (source.path ++ [index]) (.byVal expression) = .ok aliases)
    {value : Val} {runtime : DemandRuntimePoint}
    (boundary : GeneratedExpressionPrefixEnd child ⟨prior ++ map.values, map.runs⟩ cx
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial
      (lowerExpr expression (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2
      (lowerExpr expression (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1 value runtime) :
    let id := (lowerExpr expression (lowerEnv cfg.mod env.vars results)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1
    let nextPrior := prior ++ aliases.map (fun alias => (id, alias))
    GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1))
      (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).1 nextPrior ∧
    (⟨nextPrior ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env runtime ∧
    (⟨nextPrior ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
      (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2.vals.size := by
  let le := lowerEnv cfg.mod env.vars results
  let beforeArg := (lowerArgs (arguments.take index) le before).2
  let id := (lowerExpr expression le beforeArg).1
  let newRows := aliases.map (fun alias => (id, alias))
  have bound : index < arguments.length := (List.getElem?_eq_some_iff.mp found).1
  have takeEq : arguments.take (index + 1) = arguments.take index ++ [.byVal expression] := by
    rw [List.take_add_one, found]
    simp
  have argsEq : lowerArgs (arguments.take (index + 1)) le before =
      ((lowerArgs (arguments.take index) le before).1 ++ [id], (lowerExpr expression le beforeArg).2) := by
    rw [takeEq, lowerArgs_append_run]
    simp [lowerArgs, lowerArg, bind_run, pure_run, beforeArg, id]
  have nextTracked := tracked.snoc (argument := .byVal expression) (id := id) (by simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)] using query)
  have childAt := ArgSource.byVal_callChild source found child canonical
  obtain ⟨typing, roots⟩ := ArgSource.byVal_callMetadata source found child canonical
  have childQuery : child.rootsEnv.access.aliasExpr child.path expression = .ok aliases := by
    simpa only [roots, childAt.path, AccessEnv.aliasArg] using query
  have produced := boundary.canonical aliases childQuery
  have realized : (⟨newRows ++ (prior ++ map.values), map.runs⟩ : RetainedSsaMap).Realizes cfg.mod child.world env runtime :=
    RetainedSsaMap.addValues_realizes boundary.demanded.operands produced
  have nextRealized : (⟨(prior ++ newRows) ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env runtime := by
    rw [← childAt.world]
    constructor
    · intro cell member
      apply realized.1 cell
      rcases List.mem_append.mp member with old | existing
      · rcases List.mem_append.mp old with previous | added
        · exact List.mem_append_right _ (List.mem_append_left _ previous)
        · exact List.mem_append_left _ added
      · exact List.mem_append_right _ (List.mem_append_right _ existing)
    · exact realized.2
  have fresh : id < (lowerExpr expression le beforeArg).2.vals.size := boundary.post.lt (id, .val value) (by simp [id, beforeArg, le])
  have nextBounded : (⟨(prior ++ newRows) ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
      (lowerExpr expression le beforeArg).2.vals.size := by
    constructor
    · intro cell member
      simp only [List.mem_append] at member
      rcases member with (old | added) | old
      · exact boundary.bounded.1 cell (List.mem_append_left _ old)
      · obtain ⟨alias, _, rfl⟩ := List.mem_map.mp added
        exact fresh
      · exact boundary.bounded.1 cell (List.mem_append_right _ old)
    · exact boundary.bounded.2
  refine ⟨?_, nextRealized, ?_⟩
  · rw [argsEq, takeEq]
    simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound), id, newRows] using nextTracked
  · rw [argsEq]
    exact nextBounded

theorem accepted_generated_call_value_next_input {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {expression : Expr} (found : arguments[index]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    {cx : FnCtx} {results : List Ty} {before : LS} {loop : Option LoopCtx} {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    {map : RetainedSsaMap} {value : Val} {runtime : DemandRuntimePoint}
    (boundary : GeneratedExpressionPrefixEnd child map cx
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial
      (lowerExpr expression (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2
      (lowerExpr expression (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1 value runtime) :
    GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 runtime.frame runtime.point := by
  let le := lowerEnv cfg.mod env.vars results
  let beforeArg := (lowerArgs (arguments.take index) le before).2
  have takeEq : arguments.take (index + 1) = arguments.take index ++ [.byVal expression] := by
    rw [List.take_add_one, found]
    simp
  have nextBuilder : (lowerArgs (arguments.take (index + 1)) le before).2 = (lowerExpr expression le beforeArg).2 := by
    rw [takeEq, lowerArgs_append_run]
    simp [lowerArgs, lowerArg, bind_run, pure_run, beforeArg]
  rw [nextBuilder]
  have advance := advB_lowerExpr expression le beforeArg _ _ rfl
  exact ⟨input.metadata, input.loops, boundary.post.pp, boundary.post.rel, input.moduleEq, input.resultsEq,
    input.depth, (by cases loop <;> exact input.targets), input.counter.afterPost (boundary.post.sub (by simp)),
    input.generated.lowerExpr expression rfl, input.frames.mono advance.ext⟩

#print axioms accepted_generated_call_value_stage
#print axioms accepted_generated_call_value_stage_stopped
#print axioms accepted_generated_call_value_finish
#print axioms accepted_generated_call_value_next_input
end Goose.Lower
