import Goose.Lower.DemandBinaryStoppedFamily

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem accepted_generated_compare_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (operation : CmpOp) (a b : Expr)
    (leftFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop a)
    (rightFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop b) :
    GeneratedStoppedExpressionPrefixFamily cx results selected loop (.cmp operation a b) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨left, leftTyping, leftRoots, leftMetadata, rightSource⟩ := source.cmpChildren operation
  have leftOwned : GeneratedSourceOwner selected left.context :=
    (owned.child rfl 0 (.expression a) .expression rfl (by trivial)).transport
      leftMetadata.plans.symm leftMetadata.path.symm rfl leftMetadata.context.symm
  have leftOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root left.path (.expression a) before := by
    rw [leftMetadata.path]
    exact .first occurrence (.expression rfl)
  have leftRows : GeneratedDemandRows cfg.mod left.rootsEnv.access leftOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access
        (.first occurrence (.expression rfl)) required := .first (first := .expression rfl) rows
    simpa only [leftRoots, leftMetadata.path] using inherited
  have leftAdmitted : map.Admitted cfg.mod.profile left.context.retained := by
    intro profile alias member
    exact leftMetadata.retained alias (admitted profile alias member)
  have leftRealized : map.Realizes cfg.mod left.world env ⟨start, initial, state⟩ := by
    simpa only [leftMetadata.world] using realized
  have leftInput : GeneratedPrefixInput cfg env cx results loop left.typingEnv left.rootsEnv before initial start := by
    simpa only [leftTyping, leftRoots] using input
  have rightExtended : ExtT (lowerExpr b le (lowerExpr a le before).2).2 cx.fn.blocks := by
    have emitted : ExtT (emitDef ((ScalarExpression.compare operation a b).operation le before) le
        ((ScalarExpression.compare operation a b).prefix le before)).2 cx.fn.blocks := by
      simpa only [(ScalarExpression.compare operation a b).lower] using extended
    exact emitted.of_adv (adv_emitDef rfl)
  have leftExtended : ExtT (lowerExpr a le before).2 cx.fn.blocks :=
    rightExtended.of_adv (advB_lowerExpr b _ _ _ _ rfl)
  have leftDecomposed := leftFamily left leftOwned leftOccurrence leftRows coverage leftAdmitted bounded
    leftRealized leftInput leftExtended steps stopped nonTimeout
  cases leftDecomposed with
  | aborted fuel done =>
    apply StoppedExpressionPrefix.aborted (fuel + 1)
    simp [evalExpr, bind_apply, done]
  | @complete leftFuel leftCount remaining middle leftValue count leftTrace residual leftDone leftBoundary =>
    obtain ⟨right, rightTyping, rightRoots, rightMetadata⟩ := rightSource leftFuel leftValue middle.state leftDone
    have rightOwned : GeneratedSourceOwner selected right.context :=
      (owned.child rfl 1 (.expression b) .expression rfl (by trivial)).transport
        rightMetadata.plans.symm rightMetadata.path.symm rfl rightMetadata.context.symm
    have rightOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root right.path (.expression b) (lowerExpr a le before).2 := by
      rw [rightMetadata.path]
      exact .comparisonRight occurrence
    have types := comparison_operand_types operation source left right leftRoots rightRoots
    have scalar : left.ty.interiorTarget?.isSome = false := by
      rcases types with ⟨type, leftType, rightType⟩ | ⟨leftType, rightType⟩ <;> simp [leftType, Ty.interiorTarget?]
    have lookup := tyExpr_accessType (left.frame.mod_t.trans left.frame.mod_p.symm)
      (left.frame.vars_t.trans left.frame.vars_p.symm) left.typed
    have query : source.rootsEnv.access.aliasExpr (source.path ++ [0]) a = .ok [] := by
      rw [← leftRoots, ← leftMetadata.path]
      simp [AccessEnv.aliasExpr, lookup, scalar, pure, Except.pure]
    have rightRows : GeneratedDemandRows cfg.mod right.rootsEnv.access rightOccurrence required := by
      have inherited := GeneratedDemandRows.comparisonRight (aliases := []) rows query
      simpa only [rightRoots, rightMetadata.path, RetainedSsaMap.addValues, List.map_nil, List.nil_append] using inherited
    have rightAdmitted : map.Admitted cfg.mod.profile right.context.retained := by
      intro profile alias member
      exact rightMetadata.retained alias (admitted profile alias member)
    have rightRealized : map.Realizes cfg.mod right.world env middle := by
      simpa only [RetainedSsaMap.Realizes, rightMetadata.world, leftMetadata.world] using leftBoundary.demanded.operands
    have leftAdv := advB_lowerExpr a le before (lowerExpr a le before).1 (lowerExpr a le before).2 rfl
    have rightInput : GeneratedPrefixInput cfg env cx results loop right.typingEnv right.rootsEnv
        (lowerExpr a le before).2 middle.frame middle.point := by
      refine ⟨?_, ?_, leftBoundary.post.pp, leftBoundary.post.rel, input.moduleEq, input.resultsEq,
        input.depth, ?_, ?_, input.generated.lowerExpr a rfl, input.frames.mono leftAdv.ext⟩
      · simpa only [rightTyping, rightRoots] using input.metadata
      · simpa only [rightTyping] using input.loops
      · cases loop <;> exact input.targets
      · exact input.counter.afterPost (leftBoundary.post.sub (by simp))
    have rightDecomposed := rightFamily right rightOwned rightOccurrence rightRows coverage rightAdmitted leftBoundary.bounded
      rightRealized rightInput rightExtended residual stopped nonTimeout
    cases rightDecomposed with
    | aborted rightFuel rightStopped =>
      let common := max leftFuel rightFuel
      have leftDone' : evalExpr common cfg env a state = .ok leftValue middle.state :=
        ((monoAll leftFuel common (by dsimp [common]; exact Nat.le_max_left _ _)).expr cfg env a state).1 _ _ leftDone
      have rightDone' : evalExpr common cfg env b middle.state = .stop stop after := by
        rcases ((monoAll rightFuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env b middle.state).2 _ _ rightStopped with timeout | done
        · cases stop <;> simp_all [Goose.Proofs.Fuel.isTimeout]
        · exact done
      apply StoppedExpressionPrefix.aborted (common + 1)
      simp [evalExpr, bind_apply, leftDone', rightDone']
    | @complete rightFuel rightCount remaining boundary rightValue count rightTrace residual rightDone rightBoundary =>
      have leftTyped := (left.result leftFuel leftValue leftDone).typed
      have rightTyped := (right.result rightFuel rightValue rightDone).typed
      obtain ⟨inputs, leftSame, rightSame⟩ : ∃ inputs : (ScalarExpression.compare operation a b).Inputs,
          leftValue = ScalarExpression.leftValue inputs ∧ rightValue = ScalarExpression.rightValue inputs := by
        rcases types with ⟨type, leftType, rightType⟩ | ⟨leftType, rightType⟩
        · rw [leftType] at leftTyped
          rw [rightType] at rightTyped
          obtain ⟨leftNumber, rfl⟩ := hasTy_int leftTyped
          obtain ⟨rightNumber, rfl⟩ := hasTy_int rightTyped
          exact ⟨.inl (type, leftNumber, rightNumber), rfl, rfl⟩
        · rw [leftType] at leftTyped
          rw [rightType] at rightTyped
          obtain ⟨leftValue, rfl⟩ := hasTy_bool leftTyped
          obtain ⟨rightValue, rfl⟩ := hasTy_bool rightTyped
          exact ⟨.inr (leftValue, rightValue), rfl, rfl⟩
      subst leftValue rightValue
      have post := leftBoundary.post.comp rightBoundary.post
      have combinedPost : Post cfg env cx before initial ((ScalarExpression.compare operation a b).prefix le before)
          boundary.frame boundary.point ((ScalarExpression.compare operation a b).cells le before inputs) := by
        simpa only [ScalarExpression.prefix, ScalarExpression.cells, List.singleton_append] using post
      let sourceFuel := max leftFuel rightFuel
      have leftDone' : evalExpr sourceFuel cfg env a state = .ok (ScalarExpression.leftValue inputs) middle.state :=
        ((monoAll leftFuel sourceFuel (by dsimp only [sourceFuel]; exact Nat.le_max_left _ _)).expr cfg env a state).1 _ _ leftDone
      have rightDone' : evalExpr sourceFuel cfg env b middle.state = .ok (ScalarExpression.rightValue inputs) boundary.state :=
        ((monoAll rightFuel sourceFuel (by dsimp only [sourceFuel]; exact Nat.le_max_right _ _)).expr cfg env b middle.state).1 _ _ rightDone
      have evaluated : (ScalarExpression.compare operation a b).PrefixEvaluated inputs
          sourceFuel cfg env state boundary.state := ⟨middle.state, leftDone', rightDone'⟩
      have site : GeneratedScalarSite (.compare operation a b) cfg.mod source.rootsEnv.access cx.fn le
          root source.path before required boundary.point :=
        ⟨occurrence, generated_scalar_comparison_rows source inputs evaluated occurrence rows, combinedPost.pp, extended⟩
      have currentRealized : map.Realizes cfg.mod source.world env boundary := by
        simpa only [RetainedSsaMap.Realizes, rightMetadata.world] using rightBoundary.demanded.operands
      rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨rest, current, rfl, actual, tail⟩
      · obtain ⟨_, _, _, _, done, _, _⟩ := accepted_generated_scalar_runtime_stop
          (.compare operation a b) inputs source evaluated site coverage combinedPost currentRealized stopped nonTimeout
        exact .aborted (sourceFuel + 1) done
      · obtain ⟨_, _, _, _, _, _, value, _, _, _, _, done, finalBoundary⟩ :=
          accepted_generated_scalar_runtime_step (.compare operation a b) inputs source evaluated
            site coverage combinedPost rightBoundary.bounded currentRealized actual
        exact .complete (by omega) ((leftTrace.append rightTrace).append (.next actual (.zero _))) tail done finalBoundary

inductive ComparisonStoppedExpression : Expr → Prop
  | numeric {expression : Expr} (form : NumericStoppedExpression expression) : ComparisonStoppedExpression expression
  | not {expression : Expr} (child : ComparisonStoppedExpression expression) : ComparisonStoppedExpression (.not expression)
  | unary (operation : UnOp) {expression : Expr} (origin : OriginId) (child : ComparisonStoppedExpression expression) :
      ComparisonStoppedExpression (.un operation expression origin)
  | convert (kind : ConvKind) (target : IntTy) {expression : Expr} (origin : OriginId) (child : ComparisonStoppedExpression expression) :
      ComparisonStoppedExpression (.conv kind (.int target) expression origin)
  | binary (operation : BinOp) {left right : Expr} (origin : OriginId)
      (first : ComparisonStoppedExpression left) (second : ComparisonStoppedExpression right) :
      ComparisonStoppedExpression (.bin operation left right origin)
  | compare (operation : CmpOp) {left right : Expr}
      (first : ComparisonStoppedExpression left) (second : ComparisonStoppedExpression right) :
      ComparisonStoppedExpression (.cmp operation left right)

theorem accepted_generated_comparison_stopped_expressions {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {expression : Expr} (form : ComparisonStoppedExpression expression) :
    GeneratedStoppedExpressionPrefixFamily cx results selected loop expression := by
  induction form with
  | numeric form => exact accepted_generated_numeric_stopped_expressions selected loop form
  | not child ih => exact accepted_generated_not_stopped_family selected loop _ ih
  | unary operation origin child ih => exact accepted_generated_unary_stopped_family selected loop operation _ origin ih
  | convert kind target origin child ih => exact accepted_generated_convert_stopped_family selected loop kind target _ origin ih
  | binary operation origin first second firstIH secondIH =>
    exact accepted_generated_binary_stopped_family selected loop operation _ _ origin firstIH secondIH
  | compare operation first second firstIH secondIH =>
    exact accepted_generated_compare_stopped_family selected loop operation _ _ firstIH secondIH

#print axioms accepted_generated_comparison_stopped_expressions
#print axioms accepted_generated_compare_stopped_family

end Goose.Lower
