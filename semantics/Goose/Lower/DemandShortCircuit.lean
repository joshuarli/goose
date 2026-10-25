import Goose.Lower.DemandExpressionBoundary

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive ShortCircuitPath where
  | rhs
  | skip
  deriving DecidableEq

def ShortCircuitPath.leftValue (isAnd : Bool) : ShortCircuitPath → Bool
  | .rhs => isAnd
  | .skip => !isAnd

def ShortCircuitPath.target (rhs join : BlockId) : ShortCircuitPath → Pt
  | .rhs => (rhs, 0)
  | .skip => (join, 0)

def ShortCircuitPath.frame (before : GIR.Frame) (result : ValueId) (isAnd : Bool) :
    ShortCircuitPath → GIR.Frame
  | .rhs => before
  | .skip => before.set result (.val (.bool (!isAnd)))

theorem shortCircuit_control_step {isAnd : Bool} {condition : ValueId} {le : LEnv}
    {before forked : LS} {rhs join result : Nat} {point : Pt} {cx : FnCtx} {frame : GIR.Frame} {state : St}
    (path : ShortCircuitPath)
    (fork : scFork isAnd condition le before = ((rhs, join, result), forked))
    (atPoint : before.pp = some point) (extension : ExtT forked cx.fn.blocks)
    (cell : frame.vals[condition]? = some (.val (.bool (path.leftValue isAnd)))) (fuel : Nat) :
    DemandInstructionStep cx fuel ⟨point, frame, state⟩
      ⟨path.target rhs join, path.frame frame result isAnd, state⟩ := by
  obtain ⟨_, _, _, _, _, _, instruction, rhsAt, joinAt⟩ := scFork_facts fork atPoint extension
  obtain ⟨rhsBlock, rhsBlockAt, rhsParameters⟩ := extension.params rhsAt
  obtain ⟨joinBlock, joinBlockAt, joinParameters⟩ := extension.params joinAt
  let branch : DemandBranch := if isAnd then .conditional condition rhs [] join [condition]
    else .conditional condition join [condition] rhs []
  have branchAt : instAt cx.fn point = some (.term branch.term) := by
    cases isAnd <;> simpa only [instAt_eq, branch, DemandBranch.term, scTerm, ite_true,
      Bool.false_eq_true, ite_false] using instruction
  have execution : branch.enter cx.fn frame state =
      .ok ((path.target rhs join).1, instsAt cx.fn ((path.target rhs join).1, 0),
        path.frame frame result isAnd) state := by
    cases isAnd <;> cases path <;>
      simp [branch, ShortCircuitPath.leftValue, ShortCircuitPath.target, ShortCircuitPath.frame,
        DemandBranch.enter, getVal, getCell, cell, Core.expectBool, mapList, enterBlock,
        rhsBlockAt, joinBlockAt, rhsParameters, joinParameters, bindParams, setCell_eq, instsAt,
        bind_apply, pure_apply]
  have step := DemandInstructionStep.control (fuel := fuel) branchAt execution
  cases path <;> exact step

structure ShortCircuitDemandTarget {cfg : Cfg} {env : Env} {a b : Expr} {state after : St}
    {isAnd : Bool} (source : ExprSource cfg env (if isAnd then .and a b else .or a b) state)
    (right : ExprSource cfg env b after) (map : RetainedSsaMap) (cx : FnCtx)
    (path : ShortCircuitPath) (runtime : DemandRuntimePoint) : Prop where
  demanded : match path with
    | .rhs => DemandFrameAt cfg env cx right.world right.typingEnv right.rootsEnv
        right.context.inputFuture map.values map.runs runtime
    | .skip => DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
        source.context.outputFuture map.values map.runs runtime
  admitted : map.Admitted cfg.mod.profile right.context.retained
  carried : map.Realizes cfg.mod source.world env runtime

theorem accepted_shortCircuit_demand_step {cfg : Cfg} {env : Env} {a b : Expr} {state after : St}
    (isAnd : Bool) (source : ExprSource cfg env (if isAnd then .and a b else .or a b) state)
    (left : ExprSource cfg env a state) (world : left.world = source.world)
    {sourceFuel : Nat} (path : ShortCircuitPath)
    (leftDone : evalExpr sourceFuel cfg env a state = .ok (.bool (path.leftValue isAnd)) after)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {initial before forked : LS} {initialFrame frame : GIR.Frame}
    {condition : ValueId} {point : Pt} {le : LEnv} {rhs join result : Nat}
    (boundary : ExpressionDemandBoundary left map cx initial initialFrame before condition
      (.bool (path.leftValue isAnd)) after point frame)
    (fork : scFork isAnd condition le before = ((rhs, join, result), forked))
    (extension : ExtT forked cx.fn.blocks) (fuel : Nat) :
    ∃ right : ExprSource cfg env b after,
      right.world = source.world ∧ right.path = source.path ++ [1] ∧ right.plans = source.plans ∧
      HEq right.context (source.context.child rfl 1 (.expression b) .expression
        (by cases isAnd <;> rfl) (by trivial)) ∧
      DemandInstructionStep cx fuel ⟨point, frame, after⟩
        ⟨path.target rhs join, path.frame frame result isAnd, after⟩ ∧
      ShortCircuitDemandTarget source right map cx path
        ⟨path.target rhs join, path.frame frame result isAnd, after⟩ := by
  obtain ⟨canonicalLeft, _, _, _, _, _, _, _, _, next⟩ :=
    ExprSource.shortCircuitChildrenDemand isAnd source
  obtain ⟨right, _, _, _, rightWorld, rightPath, rightPlans, rightContext, rightRetained⟩ :=
    next sourceFuel (.bool (path.leftValue isAnd)) after leftDone
  have mapAdmitted : map.Admitted cfg.mod.profile right.context.retained :=
    fun shrink alias member => rightRetained alias (admitted shrink alias member)
  have realized : map.Realizes cfg.mod source.world env ⟨point, frame, after⟩ := by
    change RetainedOperandsAt cfg.mod source.world env after.store frame map.values map.runs
    simpa only [world] using boundary.demanded.operands
  have post := boundary.post
  have cell : frame.vals[condition]? = some (.val (.bool (path.leftValue isAnd))) :=
    post.has (condition, .val (.bool (path.leftValue isAnd))) (by simp)
  obtain ⟨_, _, fresh, _, stack, _, _, rhsAt, joinAt⟩ := scFork_facts fork post.pp extension
  have rhsBuilder : ({ forked with cur := some rhs } : LS).pp = some (rhs, 0) := LS.pp_cur rhsAt
  have joinBuilder : ({ forked with cur := some join } : LS).pp = some (join, 0) := LS.pp_cur joinAt
  refine ⟨right, rightWorld, rightPath, rightPlans, rightContext,
    shortCircuit_control_step path fork post.pp extension cell fuel, ?_⟩
  cases path with
  | rhs =>
    have targetRealized : map.Realizes cfg.mod right.world env ⟨(rhs, 0), frame, after⟩ := by
      simpa only [RetainedSsaMap.Realizes, rightWorld] using realized
    exact ⟨⟨⟨{ forked with cur := some rhs }, rhsBuilder, post.rel.stack_eq stack⟩,
      right.frame, targetRealized⟩, mapAdmitted, realized⟩
  | skip =>
    have done : evalExpr (sourceFuel + 1) cfg env (if isAnd then .and a b else .or a b) state =
        .ok (.bool (!isAnd)) after := by
      cases isAnd <;> simp [ShortCircuitPath.leftValue, evalExpr, leftDone, bind_apply,
        Core.expectBool, pure_apply] at *
    have output := source.result (sourceFuel + 1) (.bool (!isAnd)) done
    have same : Same before.vals.size frame (frame.set result (.val (.bool (!isAnd)))) := by
      rw [fresh]
      exact Same.set frame (Nat.le_refl _) _
    have targetRealized : map.Realizes cfg.mod source.world env
        ⟨(join, 0), frame.set result (.val (.bool (!isAnd))), after⟩ :=
      realized.retained same boundary.bounded.1 boundary.bounded.2 RetainsAliases.refl
    exact ⟨⟨⟨{ forked with cur := some join }, joinBuilder,
      (post.rel.set result _).stack_eq stack⟩, output.frame, targetRealized⟩,
      mapAdmitted, targetRealized⟩

end Goose.Lower
