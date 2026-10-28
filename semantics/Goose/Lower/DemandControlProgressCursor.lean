import Goose.Lower.DemandShortCircuitPrefixFamily
import Goose.Lower.DemandScalarDefinitionCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

structure GeneratedControlProgressCursor {cfg : Cfg} {env : Env} (cx : FnCtx)
    {expression : Expr} {state : St} (source : ExprSource cfg env expression state)
    (before _built : LS) (initial : GIR.Frame) (_start : Pt) (map _required : RetainedSsaMap)
    (runtime : DemandRuntimePoint) : Prop where
  demanded : CanonicalExpressionDemand map cx source runtime
  same : Same before.vals.size initial runtime.frame
  progress : (∃ id op, instAt cx.fn runtime.point = some (.def id op)) ∨
    ∃ next, ∀ fuel, DemandInstructionStep cx fuel runtime next

theorem accepted_generated_shortCircuit_progress_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (isAnd : Bool) (a b : Expr)
    (leftFamily : GeneratedExpressionPrefixFamily cx results selected loop a (@GeneratedControlProgressCursor cfg env cx))
    (rightFamily : GeneratedExpressionPrefixFamily cx results selected loop b (@GeneratedControlProgressCursor cfg env cx)) :
    GeneratedExpressionPrefixFamily cx results selected loop (if isAnd then .and a b else .or a b)
      (@GeneratedControlProgressCursor cfg env cx) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨left, metadata, leftOccurrence, leftRows, leftTyping, leftRoots, leftType, decomposition⟩ :=
    accepted_generated_shortCircuit_left_prefix selected loop isAnd a b leftFamily source owned occurrence rows
      coverage admitted bounded realized input extended steps
  refine ⟨owned, coverage, ?_⟩
  cases decomposition.progress with
  | interior cursor => exact .interior ⟨.child metadata cursor.demanded, cursor.same, cursor.progress⟩
  | @complete leftFuel leftCount remaining middle leftValue count leftTrace residual leftDone leftBoundary =>
    have typed := (left.result leftFuel leftValue leftDone).typed
    rw [leftType] at typed
    obtain ⟨value, rfl⟩ := hasTy_bool typed
    rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨afterBranch, entry, rfl, branch, tail⟩
    · have forkExtended := generated_shortCircuit_fork_extended (right := b) leftBoundary.post.pp extended
      have cell := leftBoundary.post.has ((lowerExpr a le before).1, .val (.bool value)) (by simp [le])
      let path : ShortCircuitPath := if value = isAnd then .rhs else .skip
      have pathValue : path.leftValue isAnd = value := by
        dsimp [path, ShortCircuitPath.leftValue]
        cases value <;> cases isAnd <;> decide
      have cell' : reached.frame.vals[(lowerExpr a le before).1]? = some (.val (.bool (path.leftValue isAnd))) := by
        simpa only [pathValue] using cell
      let forked := demandShortCircuitFork isAnd a le before
      refine .interior ⟨.child metadata (.exit leftBoundary.demanded), leftBoundary.post.same, Or.inr ?_⟩
      refine ⟨⟨path.target forked.1.1 forked.1.2.1, path.frame reached.frame forked.1.2.2 isAnd, reached.state⟩, ?_⟩
      intro fuel
      exact shortCircuit_control_step path (show scFork isAnd (lowerExpr a le before).1 le (lowerExpr a le before).2 = (forked.1, forked.2) from rfl)
        leftBoundary.post.pp forkExtended cell' fuel
    · by_cases takenRight : value = isAnd
      · subst value
        obtain ⟨right, rightTyping, rightRoots, rightType, rightMetadata, frameEq, stateEq, rightAt, rightDemand⟩ :=
          accepted_generated_shortCircuit_right_entry isAnd source left metadata leftRoots leftType leftDone
            occurrence rows coverage admitted leftBoundary extended branch
        have rightOwned : GeneratedSourceOwner selected right.context :=
          (owned.child rfl 1 (.expression b) .expression (by cases isAnd <;> rfl) (by trivial)).transport
            rightMetadata.plans.symm rightMetadata.path.symm rfl rightMetadata.context.symm
        have live : (lowerExpr a le before).2.cur.isSome = true := by
          obtain ⟨block, current, _, _⟩ := LS.pp_some leftBoundary.post.pp
          change (lowerExpr a le before).2.cur = some _ at current
          rw [current]
          rfl
        have rightOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root right.path (.expression b)
            (demandShortCircuitRightBefore isAnd a le before) := by
          rw [rightMetadata.path]
          exact .shortCircuitRight occurrence live
        have lookup := tyExpr_accessType (left.frame.mod_t.trans left.frame.mod_p.symm)
          (left.frame.vars_t.trans left.frame.vars_p.symm) left.typed
        rw [leftType] at lookup
        have query : source.rootsEnv.access.aliasExpr (source.path ++ [0]) a = .ok [] := by
          rw [← leftRoots, ← metadata.path]
          simp [AccessEnv.aliasExpr, lookup, Ty.interiorTarget?, pure, Except.pure]
        have rightRows : GeneratedDemandRows cfg.mod right.rootsEnv.access rightOccurrence required := by
          have inherited := GeneratedDemandRows.shortCircuitRight (live := live) rows query
          cases required
          simpa only [RetainedSsaMap.addValues, List.map_nil, List.nil_append, rightRoots, rightMetadata.path, demandShortCircuitRightBefore, demandShortCircuitFork] using inherited
        have rightAdmitted : map.Admitted cfg.mod.profile right.context.retained := by
          intro profile alias member
          exact rightMetadata.retained alias (admitted profile alias member)
        have forkExtended := generated_shortCircuit_fork_extended (right := b) leftBoundary.post.pp extended
        have ⟨_, _, _, valsEq, _, _, _, _, _⟩ := scFork_facts
          (show scFork isAnd (lowerExpr a le before).1 le (lowerExpr a le before).2 =
            ((demandShortCircuitFork isAnd a le before).1, (demandShortCircuitFork isAnd a le before).2) from rfl)
          leftBoundary.post.pp forkExtended
        have rightBounded : map.Bounded (demandShortCircuitRightBefore isAnd a le before).vals.size := by
          apply leftBoundary.bounded.mono
          change (lowerExpr a le before).2.vals.size ≤ (demandShortCircuitFork isAnd a le before).2.vals.size
          rw [valsEq]
          omega
        have beforeRight : before.vals.size ≤ (demandShortCircuitRightBefore isAnd a le before).vals.size := by
          change before.vals.size ≤ (demandShortCircuitFork isAnd a le before).2.vals.size
          rw [valsEq]
          have monotone : before.vals.size ≤ (lowerExpr a le before).2.vals.size := by
            simpa only [le] using leftBoundary.post.mono
          omega
        have rightRealized : map.Realizes cfg.mod right.world env ⟨entry.point, entry.frame, middle.state⟩ := by
          simpa only [RetainedSsaMap.Realizes, stateEq] using rightDemand.operands
        have rightInput : GeneratedPrefixInput cfg env cx results loop right.typingEnv right.rootsEnv
            (demandShortCircuitRightBefore isAnd a le before) entry.frame entry.point := by
          rw [frameEq]
          exact generated_shortCircuit_right_input isAnd source left right rightTyping rightRoots input leftBoundary extended rightAt
        have rightExtended := generated_shortCircuit_right_extended (right := b) leftBoundary.post.pp extended
        have entryEq : entry = ⟨entry.point, entry.frame, middle.state⟩ := by
          cases entry
          simp_all only
        have rightSteps : DemandRuntimePrefix cx afterBranch ⟨entry.point, entry.frame, middle.state⟩ reached := by
          rw [← entryEq]
          exact tail
        have rightDecomposed := rightFamily right rightOwned rightOccurrence rightRows coverage rightAdmitted rightBounded
          rightRealized rightInput rightExtended rightSteps
        cases rightDecomposed.progress with
        | interior cursor =>
          have rightSame : Same (demandShortCircuitRightBefore isAnd a le before).vals.size middle.frame reached.frame := by
            simpa only [frameEq] using cursor.same
          exact .interior ⟨.child rightMetadata cursor.demanded, leftBoundary.post.same.trans rightSame beforeRight, cursor.progress⟩
        | @complete rightFuel rightCount remaining boundary rightValue rightCountEq rightTrace residual rightDone rightBoundary =>
          have typed := (right.result rightFuel rightValue rightDone).typed
          rw [rightType] at typed
          obtain ⟨rightValue, rfl⟩ := hasTy_bool typed
          rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨remaining, final, rfl, jump, rest⟩
          · have forkExtended := generated_shortCircuit_fork_extended (right := b) leftBoundary.post.pp extended
            have jumpExtended := generated_shortCircuit_jump_extended (right := b) leftBoundary.post.pp extended
            have cell := rightBoundary.post.has
              ((lowerExpr b le (demandShortCircuitRightBefore isAnd a le before)).1, .val (.bool rightValue)) (by simp [le])
            have rightSame : Same (demandShortCircuitRightBefore isAnd a le before).vals.size middle.frame reached.frame := by
              simpa only [frameEq] using rightBoundary.post.same
            refine .interior ⟨.child rightMetadata (.exit rightBoundary.demanded), leftBoundary.post.same.trans rightSame beforeRight, Or.inr ?_⟩
            refine ⟨⟨((demandShortCircuitFork isAnd a le before).1.2.1, 0), reached.frame.set (demandShortCircuitFork isAnd a le before).1.2.2 (.val (.bool rightValue)), reached.state⟩, ?_⟩
            intro fuel
            exact shortCircuit_join_step (state := reached.state)
              (show scFork isAnd (lowerExpr a le before).1 le (lowerExpr a le before).2 =
                ((demandShortCircuitFork isAnd a le before).1, (demandShortCircuitFork isAnd a le before).2) from rfl)
              leftBoundary.post.pp forkExtended rightBoundary.post.pp jumpExtended cell fuel
          · have rightBoundary' : ExpressionDemandBoundary right map cx (demandShortCircuitRightBefore isAnd a le before) middle.frame
                (lowerExpr b le (demandShortCircuitRightBefore isAnd a le before)).2
                (lowerExpr b le (demandShortCircuitRightBefore isAnd a le before)).1 (.bool rightValue)
                boundary.state boundary.point boundary.frame := by
              simpa only [frameEq] using rightBoundary
            obtain ⟨fuel, done, finalBoundary⟩ := accepted_shortCircuit_right_boundary isAnd source left right leftDone rightDone
              admitted bounded realized leftBoundary rightBoundary' extended jump
            have rightCombined := rightTrace.append (.next jump (.zero _))
            rw [← entryEq] at rightCombined
            have combined := leftTrace.append (.next branch rightCombined)
            exact .complete (by omega) combined rest done finalBoundary
      · have skip : value = !isAnd := by cases value <;> cases isAnd <;> simp_all
        subst value
        obtain ⟨done, finalBoundary⟩ := accepted_shortCircuit_skip_boundary isAnd source left leftDone admitted bounded
          realized leftBoundary extended branch
        exact .complete (by omega) (leftTrace.append (.next branch (.zero _))) tail done finalBoundary


theorem accepted_generated_control_progress_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {expression : Expr} (form : ControlPrefixExpression expression) :
    GeneratedExpressionPrefixFamily cx results selected loop expression (@GeneratedControlProgressCursor cfg env cx) := by
  induction form with
  | scalar form =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_scalar_definition_prefix_family selected loop form)
    intro expression state source before built initial start map required runtime cursor
    exact ⟨cursor.demanded, cursor.same, Or.inl cursor.instruction⟩
  | and first second firstIH secondIH =>
    exact accepted_generated_shortCircuit_progress_family selected loop true _ _ firstIH secondIH
  | or first second firstIH secondIH =>
    exact accepted_generated_shortCircuit_progress_family selected loop false _ _ firstIH secondIH
  | not child ih =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_not_prefix_family selected loop _ _ ih)
    intro expression state source before built initial start map required runtime cursor
    have demanded := cursor.canonical (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded)
    have same := cursor.same (by intro expression state child before built initial start map required runtime cursor; exact cursor.same)
    cases cursor with
    | child child metadata owned occurrence rows coverage cursor => exact ⟨demanded, same, cursor.progress⟩
    | operation child metadata owned site coverage admitted bounded same carried => exact ⟨demanded, same, Or.inl ⟨_, _, site.instruction⟩⟩
  | unary operation origin child ih =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_unary_prefix_family selected loop operation _ origin _ ih)
    intro expression state source before built initial start map required runtime cursor
    have demanded := cursor.canonical (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded)
    have same := cursor.same (by intro expression state child before built initial start map required runtime cursor; exact cursor.same)
    cases cursor with
    | child child metadata owned occurrence rows coverage cursor => exact ⟨demanded, same, cursor.progress⟩
    | operation child metadata owned site coverage admitted bounded same carried => exact ⟨demanded, same, Or.inl ⟨_, _, site.instruction⟩⟩
  | convert kind target origin child ih =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_convert_prefix_family selected loop kind target _ origin _ ih)
    intro expression state source before built initial start map required runtime cursor
    have demanded := cursor.canonical (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded)
    have same := cursor.same (by intro expression state child before built initial start map required runtime cursor; exact cursor.same)
    cases cursor with
    | child child metadata owned occurrence rows coverage cursor => exact ⟨demanded, same, cursor.progress⟩
    | operation child metadata owned site coverage admitted bounded same carried => exact ⟨demanded, same, Or.inl ⟨_, _, site.instruction⟩⟩
  | binary operation origin first second firstIH secondIH =>
    apply GeneratedExpressionPrefixFamily.mapCursor
      (accepted_generated_binary_prefix_family selected loop operation _ _ origin _ _ firstIH secondIH)
    intro expression state source before built initial start map required runtime cursor
    have demanded := cursor.canonical (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded) (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded)
    have same := cursor.same (by intro expression state child before built initial start map required runtime cursor; exact cursor.same) (by intro expression state child before built initial start map required runtime cursor; exact cursor.same)
    cases cursor with
    | left child metadata owned occurrence rows coverage cursor => exact ⟨demanded, same, cursor.progress⟩
    | right child metadata owned occurrence rows coverage leftPost cursor => exact ⟨demanded, same, cursor.progress⟩
    | operation child metadata owned site coverage admitted bounded same carried => exact ⟨demanded, same, Or.inl ⟨_, _, site.instruction⟩⟩
  | compare operation first second firstIH secondIH =>
    apply GeneratedExpressionPrefixFamily.mapCursor
      (accepted_generated_compare_prefix_family selected loop operation _ _ _ _ firstIH secondIH)
    intro expression state source before built initial start map required runtime cursor
    have demanded := cursor.canonical (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded) (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded)
    have same := cursor.same (by intro expression state child before built initial start map required runtime cursor; exact cursor.same) (by intro expression state child before built initial start map required runtime cursor; exact cursor.same)
    cases cursor with
    | left child metadata owned occurrence rows coverage cursor => exact ⟨demanded, same, cursor.progress⟩
    | right child metadata owned occurrence rows coverage leftPost cursor => exact ⟨demanded, same, cursor.progress⟩
    | operation child metadata owned site coverage admitted bounded same carried => exact ⟨demanded, same, Or.inl ⟨_, _, site.instruction⟩⟩

#print axioms accepted_generated_control_progress_prefix_family

#print axioms accepted_generated_shortCircuit_progress_family
end Goose.Lower
