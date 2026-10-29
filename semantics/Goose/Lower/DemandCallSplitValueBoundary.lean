import Goose.Lower.DemandCallSplitCoverage
import Goose.Lower.DemandGeneratedExpressionPrefix
import Goose.Lower.DemandCallValueStage

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Lower.Validation.ReplacementContentFlowSource

theorem SplitCallRetained.byValBoundary {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {expression : Expr} (found : arguments[index]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext root.world root.typingEnv root.rootsEnv
      (callArgContext root.context index (.byVal expression) found))
    {cx : FnCtx} {before built : LS} {initial : GIR.Frame} {id : ValueId} {value : Val} {runtime : DemandRuntimePoint}
    {map : RetainedSsaMap} {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell}
    (boundary : GeneratedExpressionPrefixEnd child ⟨values ++ map.values, map.runs⟩ cx before initial built id value runtime)
    (checked : ∀ cell ∈ slots, cell.Checked root index initial)
    (bounded : ∀ cell ∈ slots, cell.value < before.vals.size) :
    (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes cfg.mod root.world env runtime ∧
      ∀ cell ∈ slots, cell.Checked root (index + 1) runtime.frame := by
  have metadata := ArgSource.byVal_callMetadata root found child canonical
  obtain ⟨plans, path, world, typing, roots, childContext⟩ := canonical
  have contextEq : HEq child.context
      (root.context.child rfl index (.expression expression) .expression
        (by simp [DemandNode.child?, DemandNode.children, found]) (by trivial)) := by
    simpa only [ArgSource.MatchesContext, callArgContext] using childContext
  have futureEq := demandContextOutputFutureEq plans path rfl contextEq
  have sourceFrame : Core.Sound.Frame cfg.mod root.world root.typingEnv root.rootsEnv env runtime.state
      (callArgContext root.context index (.byVal expression) found).outputFuture := by
    have result := boundary.demanded.source
    rw [world, metadata.1, metadata.2] at result
    simpa only [futureEq, callArgContext, ArgContext.outputFuture] using result
  constructor
  · constructor
    · simpa only [RetainedSsaMap.Realizes, world] using boundary.demanded.operands
    · exact SliceSlotArgumentCells.ofLaterArgumentOutput root found boundary.post sourceFrame slots checked bounded
  · intro cell member
    exact SliceSlotArgumentCell.advance (checked cell member) (by omega) boundary.post (bounded cell member)

#print axioms SplitCallRetained.byValBoundary
theorem accepted_generated_call_split_value_finish {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {expression : Expr} (found : arguments[index]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byVal expression) found))
    {cx : FnCtx} {results : List Ty} {before : LS} {initial : GIR.Frame} {map : RetainedSsaMap}
    {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell}
    (split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 values slots)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasArg (source.path ++ [index]) (.byVal expression) = .ok aliases)
    {value : Val} {runtime : DemandRuntimePoint}
    (boundary : GeneratedExpressionPrefixEnd child ⟨values ++ map.values, map.runs⟩ cx
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial
      (lowerExpr expression (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2
      (lowerExpr expression (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1 value runtime)
    (checked : ∀ cell ∈ slots, cell.Checked source index initial)
    (bounded : ∀ cell ∈ slots, cell.value <
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size) :
    let id := (lowerExpr expression (lowerEnv cfg.mod env.vars results)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1
    let nextValues := values ++ aliases.map (fun alias => (id, alias))
    SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1))
      (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).1 nextValues slots ∧
    (⟨⟨nextValues ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes cfg.mod source.world env runtime ∧
    (⟨⟨nextValues ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
      (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
    ∀ cell ∈ slots, cell.Checked source (index + 1) runtime.frame := by
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
  have ordinary : OrdinaryCallArgument source.rootsEnv.access (.byVal expression) := by
    rintro ⟨borrow, place, mutability, element, same, type⟩
    cases same
  have nextRows := split.snocValue (id := id) ordinary (by simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)] using query)
  have childAt := ArgSource.byVal_callChild source found child canonical
  obtain ⟨typing, roots⟩ := ArgSource.byVal_callMetadata source found child canonical
  have childQuery : child.rootsEnv.access.aliasExpr child.path expression = .ok aliases := by
    simpa only [roots, childAt.path, AccessEnv.aliasArg] using query
  have produced := boundary.canonical aliases childQuery
  rw [childAt.world] at produced
  obtain ⟨carried, nextChecked⟩ := SplitCallRetained.byValBoundary source found child canonical boundary checked bounded
  have withValues := RetainedSsaMap.addValues_realizes (id := id) (aliases := aliases) carried.1 produced
  have nextRealized : (⟨(values ++ newRows) ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod source.world env runtime := by
    constructor
    · intro cell member
      apply withValues.1 cell
      rcases List.mem_append.mp member with old | existing
      · rcases List.mem_append.mp old with previous | added
        · exact List.mem_append_right _ (List.mem_append_left _ previous)
        · exact List.mem_append_left _ added
      · exact List.mem_append_right _ (List.mem_append_right _ existing)
    · exact withValues.2
  have fresh : id < (lowerExpr expression le beforeArg).2.vals.size := boundary.post.lt (id, .val value) (by simp [id, beforeArg, le])
  have nextBounded : (⟨(values ++ newRows) ++ map.values, map.runs⟩ : RetainedSsaMap).Bounded
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
  refine ⟨?_, ⟨nextRealized, carried.2⟩, ?_, nextChecked⟩
  · rw [argsEq, takeEq]
    simpa [id, newRows] using nextRows
  · rw [argsEq]
    exact ⟨nextBounded, fun cell member => Nat.lt_of_lt_of_le (bounded cell member) boundary.post.mono⟩

#print axioms accepted_generated_call_split_value_finish

end Goose.Lower
