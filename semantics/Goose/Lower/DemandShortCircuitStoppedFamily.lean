import Goose.Lower.DemandCompareStoppedFamily
import Goose.Lower.DemandShortCircuitJoin

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem accepted_generated_shortCircuit_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (isAnd : Bool) (a b : Expr)
    (leftFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop a)
    (rightFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop b) :
    GeneratedStoppedExpressionPrefixFamily cx results selected loop (if isAnd then .and a b else .or a b) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨left, leftTyping, leftRoots, leftType, world, path, plans, context, retained, next⟩ := source.shortCircuitChildrenDemand isAnd
  have metadata : source.ChildAt left 0 (by cases isAnd <;> rfl) := ⟨world, path, plans, context, leftTyping, leftRoots, retained⟩
  have leftOwned : GeneratedSourceOwner selected left.context :=
    (owned.child rfl 0 (.expression a) .expression (by cases isAnd <;> rfl) (by trivial)).transport
      plans.symm path.symm rfl context.symm
  have leftOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root left.path (.expression a) before := by
    rw [path]
    exact .first occurrence (.expression (by cases isAnd <;> rfl))
  have leftRows : GeneratedDemandRows cfg.mod left.rootsEnv.access leftOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access
      (.first occurrence (.expression (by cases isAnd <;> rfl))) required :=
        .first (first := .expression (by cases isAnd <;> rfl)) rows
    simpa only [leftRoots, path] using inherited
  have leftAdmitted : map.Admitted cfg.mod.profile left.context.retained := by
    intro profile alias member
    exact retained alias (admitted profile alias member)
  have leftRealized : map.Realizes cfg.mod left.world env ⟨start, initial, state⟩ := by
    simpa only [world] using realized
  have leftInput : GeneratedPrefixInput cfg env cx results loop left.typingEnv left.rootsEnv before initial start := by
    simpa only [leftTyping, leftRoots] using input
  have leftExtended : ExtT (lowerExpr a le before).2 cx.fn.blocks := by
    cases isAnd <;> simp only [Bool.false_eq_true, ite_false, ite_true, lowerExpr, bind_run] at extended
    all_goals exact extended.of_adv (advB_shortCircuit _ _ (advB_lowerExpr b) _ _ _ _ rfl)
  have decomposition := leftFamily left leftOwned leftOccurrence leftRows coverage leftAdmitted bounded
    leftRealized leftInput leftExtended steps stopped nonTimeout
  cases decomposition with
  | aborted fuel done =>
    apply StoppedExpressionPrefix.aborted (fuel + 1)
    cases isAnd <;> simp [evalExpr, bind_apply, done]
  | @complete leftFuel leftCount remaining middle leftValue count leftTrace residual leftDone leftBoundary =>
    have typed := (left.result leftFuel leftValue leftDone).typed
    rw [leftType] at typed
    obtain ⟨value, rfl⟩ := hasTy_bool typed
    rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨afterBranch, entry, rfl, branch, tail⟩
    · have forkExtended := generated_shortCircuit_fork_extended (right := b) leftBoundary.post.pp extended
      have instruction := (scFork_facts
        (show scFork isAnd (lowerExpr a le before).1 le (lowerExpr a le before).2 =
          ((demandShortCircuitFork isAnd a le before).1, (demandShortCircuitFork isAnd a le before).2) from rfl)
        leftBoundary.post.pp forkExtended).2.2.2.2.2.2.1
      have instruction : instAt cx.fn reached.point = some (.term (scTerm isAnd (lowerExpr a le before).1
          (demandShortCircuitFork isAnd a le before).1.1 (demandShortCircuitFork isAnd a le before).1.2.1)) := by
        simpa only [instAt_eq] using instruction
      cases stopped with
      | timeout => exact (nonTimeout rfl).elim
      | definition actual execution => cases instruction.symm.trans actual
      | effect actual execution => cases instruction.symm.trans actual
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
          rightRealized rightInput rightExtended rightSteps stopped nonTimeout
        cases rightDecomposed with
        | aborted rightFuel rightStopped =>
          let common := max leftFuel rightFuel
          have leftDone' : evalExpr common cfg env a state = .ok (.bool isAnd) middle.state :=
            ((monoAll leftFuel common (by dsimp [common]; exact Nat.le_max_left _ _)).expr cfg env a state).1 _ _ leftDone
          have rightDone' : evalExpr common cfg env b middle.state = .stop stop after := by
            rcases ((monoAll rightFuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env b middle.state).2 _ _ rightStopped with timeout | done
            · have isNotTimeout : Goose.Proofs.Fuel.isTimeout stop = false := by
                cases stop with
                | timeout => exact (nonTimeout rfl).elim
                | abort | exit | fault => rfl
              rw [isNotTimeout] at timeout
              cases timeout
            · exact done
          apply StoppedExpressionPrefix.aborted (common + 1)
          cases isAnd <;> simp [evalExpr, bind_apply, leftDone', rightDone', Core.expectBool, pure_apply]
        | @complete rightFuel rightCount remaining boundary rightValue rightCountEq rightTrace residual rightDone rightBoundary =>
          have typed := (right.result rightFuel rightValue rightDone).typed
          rw [rightType] at typed
          obtain ⟨rightValue, rfl⟩ := hasTy_bool typed
          rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨remaining, final, rfl, jump, rest⟩
          · have forkExtended := generated_shortCircuit_fork_extended (right := b) leftBoundary.post.pp extended
            have jumpExtended := generated_shortCircuit_jump_extended (right := b) leftBoundary.post.pp extended
            have cell := rightBoundary.post.has
              ((lowerExpr b le (demandShortCircuitRightBefore isAnd a le before)).1, .val (.bool rightValue)) (by simp [le])
            have expected := shortCircuit_join_step (state := reached.state)
              (show scFork isAnd (lowerExpr a le before).1 le (lowerExpr a le before).2 =
                ((demandShortCircuitFork isAnd a le before).1, (demandShortCircuitFork isAnd a le before).2) from rfl)
              leftBoundary.post.pp forkExtended rightBoundary.post.pp jumpExtended cell targetFuel
            exact (stopped.excludes_step_nonTimeout nonTimeout expected).elim
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

inductive ControlStoppedExpression : Expr → Prop
  | comparison {expression : Expr} (form : ComparisonStoppedExpression expression) : ControlStoppedExpression expression
  | not {expression : Expr} (child : ControlStoppedExpression expression) : ControlStoppedExpression (.not expression)
  | unary (operation : UnOp) {expression : Expr} (origin : OriginId) (child : ControlStoppedExpression expression) :
      ControlStoppedExpression (.un operation expression origin)
  | convert (kind : ConvKind) (target : IntTy) {expression : Expr} (origin : OriginId) (child : ControlStoppedExpression expression) :
      ControlStoppedExpression (.conv kind (.int target) expression origin)
  | binary (operation : BinOp) {left right : Expr} (origin : OriginId)
      (first : ControlStoppedExpression left) (second : ControlStoppedExpression right) :
      ControlStoppedExpression (.bin operation left right origin)
  | compare (operation : CmpOp) {left right : Expr}
      (first : ControlStoppedExpression left) (second : ControlStoppedExpression right) :
      ControlStoppedExpression (.cmp operation left right)
  | and {left right : Expr} (first : ControlStoppedExpression left) (second : ControlStoppedExpression right) :
      ControlStoppedExpression (.and left right)
  | or {left right : Expr} (first : ControlStoppedExpression left) (second : ControlStoppedExpression right) :
      ControlStoppedExpression (.or left right)

theorem accepted_generated_control_stopped_expressions {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {expression : Expr} (form : ControlStoppedExpression expression) :
    GeneratedStoppedExpressionPrefixFamily cx results selected loop expression := by
  induction form with
  | comparison form => exact accepted_generated_comparison_stopped_expressions selected loop form
  | not child ih => exact accepted_generated_not_stopped_family selected loop _ ih
  | unary operation origin child ih => exact accepted_generated_unary_stopped_family selected loop operation _ origin ih
  | convert kind target origin child ih => exact accepted_generated_convert_stopped_family selected loop kind target _ origin ih
  | binary operation origin first second firstIH secondIH =>
    exact accepted_generated_binary_stopped_family selected loop operation _ _ origin firstIH secondIH
  | compare operation first second firstIH secondIH =>
    exact accepted_generated_compare_stopped_family selected loop operation _ _ firstIH secondIH
  | and first second firstIH secondIH =>
    exact accepted_generated_shortCircuit_stopped_family selected loop true _ _ firstIH secondIH
  | or first second firstIH secondIH =>
    exact accepted_generated_shortCircuit_stopped_family selected loop false _ _ firstIH secondIH

#print axioms accepted_generated_control_stopped_expressions
#print axioms accepted_generated_shortCircuit_stopped_family

end Goose.Lower
