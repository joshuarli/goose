import Goose.Lower.DemandGeneratedScalarPrefix
import Goose.Lower.DemandGeneratedShortCircuit

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_shortCircuit_left_prefix {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (isAnd : Bool) (a b : Expr)
    (leftFamily : GeneratedExpressionPrefixFamily cx results selected loop a (@CanonicalExpressionPrefixCursor cfg env cx))
    {state : St} (source : ExprSource cfg env (if isAnd then .and a b else .or a b) state) {before : LS}
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (if isAnd then .and a b else .or a b)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (if isAnd then .and a b else .or a b)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    ∃ (left : ExprSource cfg env a state)
      (_metadata : source.ChildAt left 0 (by cases isAnd <;> rfl))
      (leftOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root left.path (.expression a) before)
      (leftRows : GeneratedDemandRows cfg.mod left.rootsEnv.access leftOccurrence required),
      left.ty = .bool ∧
      GeneratedExpressionPrefixDecomposition left selected leftOccurrence leftRows map initial start
        (CanonicalExpressionPrefixCursor cx left before (lowerExpr a (lowerEnv cfg.mod env.vars results) before).2
          initial start map required) taken reached := by
  obtain ⟨left, typing, roots, type, world, path, plans, context, retained, next⟩ := source.shortCircuitChildrenDemand isAnd
  have metadata : source.ChildAt left 0 (by cases isAnd <;> rfl) := ⟨world, path, plans, context, retained⟩
  have leftOwned : GeneratedSourceOwner selected left.context :=
    (owned.child rfl 0 (.expression a) .expression (by cases isAnd <;> rfl) (by trivial)).transport
      plans.symm path.symm rfl context.symm
  have leftOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root left.path (.expression a) before := by
    rw [path]
    exact .first occurrence (.expression (by cases isAnd <;> rfl))
  have leftRows : GeneratedDemandRows cfg.mod left.rootsEnv.access leftOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access
      (.first occurrence (.expression (by cases isAnd <;> rfl))) required :=
        .first (first := .expression (by cases isAnd <;> rfl)) rows
    simpa only [roots, path] using inherited
  have leftAdmitted : map.Admitted cfg.mod.profile left.context.retained := by
    intro profile alias member
    exact retained alias (admitted profile alias member)
  have leftRealized : map.Realizes cfg.mod left.world env ⟨start, initial, state⟩ := by
    simpa only [world] using realized
  have leftInput : GeneratedPrefixInput cfg env cx results loop left.typingEnv left.rootsEnv before initial start := by
    simpa only [typing, roots] using input
  have leftExtended : ExtT (lowerExpr a (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks := by
    cases isAnd <;> simp only [Bool.false_eq_true, ite_false, ite_true, lowerExpr, bind_run] at extended
    all_goals exact extended.of_adv (advB_shortCircuit _ _ (advB_lowerExpr b) _ _ _ _ rfl)
  exact ⟨left, metadata, leftOccurrence, leftRows, type,
    leftFamily left leftOwned leftOccurrence leftRows coverage leftAdmitted bounded leftRealized leftInput leftExtended steps⟩

theorem accepted_generated_shortCircuit_actual_branch {cfg : Cfg} {env : Env} {a b : Expr} {state after : St}
    (isAnd : Bool) (source : ExprSource cfg env (if isAnd then .and a b else .or a b) state)
    (left : ExprSource cfg env a state) (metadata : source.ChildAt left 0 (by cases isAnd <;> rfl))
    (roots : left.rootsEnv = source.rootsEnv) (leftType : left.ty = .bool)
    {sourceFuel : Nat} {value : Bool} (leftDone : evalExpr sourceFuel cfg env a state = .ok (.bool value) after)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS} {point : Pt}
    {initial frame : GIR.Frame} {map required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root source.path
      (.expression (if isAnd then .and a b else .or a b)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (boundary : ExpressionDemandBoundary left map cx before initial (lowerExpr a le before).2
      (lowerExpr a le before).1 (.bool value) after point frame)
    (extended : ExtT (lowerExpr (if isAnd then .and a b else .or a b) le before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame} {nextState : St}
    (actual : Evidence.RuntimeStep cx.cfg cx.fn point frame after next nextFrame nextState) :
    ∃ path : ShortCircuitPath, ∃ right : ExprSource cfg env b after,
      path.leftValue isAnd = value ∧ right.world = source.world ∧ right.path = source.path ++ [1] ∧
      right.plans = source.plans ∧
      HEq right.context (source.context.child rfl 1 (.expression b) .expression
        (by cases isAnd <;> rfl) (by trivial)) ∧
      let fork := demandShortCircuitFork isAnd a le before
      next = path.target fork.1.1 fork.1.2.1 ∧ nextFrame = path.frame frame fork.1.2.2 isAnd ∧ nextState = after ∧
      (match path with
      | .rhs => DemandFrameAt cfg env cx right.world right.typingEnv right.rootsEnv
          right.context.inputFuture map.values map.runs ⟨next, nextFrame, nextState⟩
      | .skip => DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
          source.context.outputFuture map.values map.runs ⟨next, nextFrame, nextState⟩) := by
  let path : ShortCircuitPath := if value = isAnd then .rhs else .skip
  have valueEq : path.leftValue isAnd = value := by cases isAnd <;> cases value <;> rfl
  have lookup := tyExpr_accessType (left.frame.mod_t.trans left.frame.mod_p.symm)
    (left.frame.vars_t.trans left.frame.vars_p.symm) left.typed
  rw [leftType] at lookup
  have query : source.rootsEnv.access.aliasExpr (source.path ++ [0]) a = .ok [] := by
    rw [← roots, ← metadata.path]
    simp [AccessEnv.aliasExpr, lookup, Ty.interiorTarget?, pure, Except.pure]
  have forkExtended := generated_shortCircuit_fork_extended (right := b) boundary.post.pp extended
  have done : evalExpr sourceFuel cfg env a state = .ok (.bool (path.leftValue isAnd)) after := by
    rw [valueEq]
    exact leftDone
  have adjusted : ExpressionDemandBoundary left map cx before initial (lowerExpr a le before).2
      (lowerExpr a le before).1 (.bool (path.leftValue isAnd)) after point frame := by
    rw [valueEq]
    exact boundary
  obtain ⟨fuel, actualStep⟩ := runtimeStep_demandInstructionStep actual
  obtain ⟨site, covered, right, world, rightPath, plans, context, leftBounded, rightBounded, rightAdmitted, expected, demanded, carried⟩ :=
    accepted_generated_shortCircuit_branch isAnd source left metadata.world roots metadata.path leftType path done
      occurrence rows coverage admitted query adjusted forkExtended fuel
  have same := actualStep.deterministic expected
  have nextEq := congrArg DemandRuntimePoint.point same
  have frameEq := congrArg DemandRuntimePoint.frame same
  have stateEq := congrArg DemandRuntimePoint.state same
  dsimp only at nextEq frameEq stateEq
  refine ⟨path, right, valueEq, world, rightPath, plans, context, nextEq, frameEq, stateEq, ?_⟩
  rw [nextEq, frameEq, stateEq]
  cases h : path <;> simp only [h, RetainedSsaMap.addValues, List.map_nil, List.nil_append] at demanded ⊢ <;> exact demanded

theorem accepted_generated_shortCircuit_right_entry {cfg : Cfg} {env : Env} {a b : Expr} {state middle : St}
    (isAnd : Bool) (source : ExprSource cfg env (if isAnd then .and a b else .or a b) state)
    (left : ExprSource cfg env a state) (metadata : source.ChildAt left 0 (by cases isAnd <;> rfl))
    (roots : left.rootsEnv = source.rootsEnv) (leftType : left.ty = .bool)
    {sourceFuel : Nat} (leftDone : evalExpr sourceFuel cfg env a state = .ok (.bool isAnd) middle)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS} {point : Pt}
    {initial frame : GIR.Frame} {map required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root source.path
      (.expression (if isAnd then .and a b else .or a b)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (boundary : ExpressionDemandBoundary left map cx before initial (lowerExpr a le before).2
      (lowerExpr a le before).1 (.bool isAnd) middle point frame)
    (extended : ExtT (lowerExpr (if isAnd then .and a b else .or a b) le before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame} {nextState : St}
    (actual : Evidence.RuntimeStep cx.cfg cx.fn point frame middle next nextFrame nextState) :
    ∃ right : ExprSource cfg env b middle,
      right.typingEnv = source.typingEnv ∧ right.rootsEnv = source.rootsEnv ∧ right.ty = .bool ∧
      source.ChildAt right 1 (by cases isAnd <;> rfl) ∧ nextFrame = frame ∧ nextState = middle ∧
      (demandShortCircuitRightBefore isAnd a le before).pp = some next ∧
      DemandFrameAt cfg env cx right.world right.typingEnv right.rootsEnv right.context.inputFuture
        map.values map.runs ⟨next, nextFrame, nextState⟩ := by
  obtain ⟨path, branchRight, valueEq, branchWorld, branchPath, branchPlans, branchContext,
    nextEq, frameEq, stateEq, branchDemand⟩ :=
    accepted_generated_shortCircuit_actual_branch isAnd source left metadata roots leftType leftDone
      occurrence rows coverage admitted boundary extended actual
  have rhs : path = .rhs := by
    cases h : path <;> cases isAnd <;> simp [h, ShortCircuitPath.leftValue] at valueEq ⊢
  subst path
  dsimp only [ShortCircuitPath.target, ShortCircuitPath.frame] at nextEq frameEq
  obtain ⟨_, _, _, _, _, _, _, _, _, nextSource⟩ := source.shortCircuitChildrenDemand isAnd
  obtain ⟨right, typing, rightRoots, type, world, path, plans, context, retained⟩ :=
    nextSource sourceFuel (.bool isAnd) middle leftDone
  have child : source.ChildAt right 1 (by cases isAnd <;> rfl) := ⟨world, path, plans, context, retained⟩
  have forkExtended := generated_shortCircuit_fork_extended (right := b) boundary.post.pp extended
  have ⟨_, _, _, _, _, _, _, rhsAt, _⟩ := scFork_facts
    (show scFork isAnd (lowerExpr a le before).1 le (lowerExpr a le before).2 =
      ((demandShortCircuitFork isAnd a le before).1, (demandShortCircuitFork isAnd a le before).2) from rfl)
    boundary.post.pp forkExtended
  have atPoint : (demandShortCircuitRightBefore isAnd a le before).pp = some next := by
    rw [nextEq]
    exact LS.pp_cur rhsAt
  have branchBuilder := branchDemand.builder
  have branchRealized := branchDemand.operands
  rw [stateEq] at branchRealized
  have rightRealized : map.Realizes cfg.mod right.world env ⟨next, nextFrame, middle⟩ := by
    simpa only [RetainedSsaMap.Realizes, world, branchWorld] using branchRealized
  have demanded : DemandFrameAt cfg env cx right.world right.typingEnv right.rootsEnv right.context.inputFuture
      map.values map.runs ⟨next, nextFrame, nextState⟩ := by
    rw [stateEq]
    exact ⟨branchBuilder, right.frame, rightRealized⟩
  exact ⟨right, typing, rightRoots, type, child, frameEq, stateEq, atPoint, demanded⟩

#print axioms accepted_generated_shortCircuit_right_entry

#print axioms accepted_generated_shortCircuit_actual_branch

#print axioms accepted_generated_shortCircuit_left_prefix

end Goose.Lower
