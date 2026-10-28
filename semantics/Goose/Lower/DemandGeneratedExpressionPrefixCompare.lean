import Goose.Lower.DemandGeneratedExpressionPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem comparison_operand_types {cfg : Cfg} {env : Env} {a b : Expr} {state after : St} (op : CmpOp)
    (source : ExprSource cfg env (.cmp op a b) state) (left : ExprSource cfg env a state)
    (right : ExprSource cfg env b after)
    (leftRoots : left.rootsEnv = source.rootsEnv)
    (rightRoots : right.rootsEnv = source.rootsEnv) :
    (∃ ty, left.ty = .int ty ∧ right.ty = .int ty) ∨ (left.ty = .bool ∧ right.ty = .bool) := by
  have ht := source.typed
  simp only [tyExpr] at ht
  simp only [chk] at ht
  obtain ⟨ta, t1, hta, tb, t2, htb, hcompare⟩ := ht
  have modEq := source.frame.mod_t.trans source.frame.mod_p.symm
  have varsEq := source.frame.vars_t.trans source.frame.vars_p.symm
  have leftExpected := tyExpr_accessType modEq varsEq hta
  have rightExpected := tyExpr_accessType modEq varsEq htb
  have leftActual := tyExpr_accessType (left.frame.mod_t.trans left.frame.mod_p.symm)
    (left.frame.vars_t.trans left.frame.vars_p.symm) left.typed
  have rightActual := tyExpr_accessType (right.frame.mod_t.trans right.frame.mod_p.symm)
    (right.frame.vars_t.trans right.frame.vars_p.symm) right.typed
  rw [leftRoots] at leftActual
  rw [rightRoots] at rightActual
  have leftEq : ta = left.ty := Option.some.inj (leftExpected.symm.trans leftActual)
  have rightEq : tb = right.ty := Option.some.inj (rightExpected.symm.trans rightActual)
  subst ta tb
  cases leftTy : left.ty <;> cases rightTy : right.ty <;> simp only [leftTy, rightTy] at hcompare ⊢
  all_goals try (change Except.error _ = Except.ok _ at hcompare; cases hcompare)
  all_goals try (exact Or.inr ⟨True.intro, True.intro⟩)
  all_goals
    split at hcompare
    next same => subst_vars; exact Or.inl ⟨_, rfl, rfl⟩
    next different => change Except.error _ = Except.ok _ at hcompare; cases hcompare

inductive GeneratedExpressionPrefixCompareCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (leftCursor rightCursor : ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) :
    ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | left {operation : CmpOp} {a b : Expr} {state : St}
      {source : ExprSource cfg env (.cmp operation a b) state}
      {before : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env a state) (metadata : source.ChildAt child 0 rfl)
      (owned : GeneratedSourceOwner selected child.context)
      (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root child.path (.expression a) before)
      (rows : GeneratedDemandRows cfg.mod child.rootsEnv.access occurrence required)
      (coverage : map.Covers required)
      (demanded : leftCursor child before (lowerExpr a (lowerEnv cfg.mod env.vars results) before).2
        initial start map required runtime) :
      GeneratedExpressionPrefixCompareCursor cx results selected leftCursor rightCursor source before
        (lowerExpr (.cmp operation a b) (lowerEnv cfg.mod env.vars results) before).2 initial start map required runtime
  | right {operation : CmpOp} {a b : Expr} {state afterLeft : St}
      {source : ExprSource cfg env (.cmp operation a b) state}
      {before : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      {middleFrame : GIR.Frame} {middle : Pt}
      (child : ExprSource cfg env b afterLeft) (metadata : source.ChildAt child 1 rfl)
      (owned : GeneratedSourceOwner selected child.context)
      (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root child.path (.expression b) (lowerExpr a (lowerEnv cfg.mod env.vars results) before).2)
      (rows : GeneratedDemandRows cfg.mod child.rootsEnv.access occurrence required)
      (coverage : map.Covers required)
      (leftPost : ∃ cells, Post cfg env cx before initial
        (lowerExpr a (lowerEnv cfg.mod env.vars results) before).2 middleFrame middle cells)
      (demanded : rightCursor child (lowerExpr a (lowerEnv cfg.mod env.vars results) before).2
        (lowerExpr b (lowerEnv cfg.mod env.vars results) (lowerExpr a (lowerEnv cfg.mod env.vars results) before).2).2
        middleFrame middle map required runtime) :
      GeneratedExpressionPrefixCompareCursor cx results selected leftCursor rightCursor source before
        (lowerExpr (.cmp operation a b) (lowerEnv cfg.mod env.vars results) before).2 initial start map required runtime
  | operation {operation : CmpOp} {a b : Expr} {state afterLeft : St}
      {source : ExprSource cfg env (.cmp operation a b) state}
      {before : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env b afterLeft) (metadata : source.ChildAt child 1 rfl)
      (owned : GeneratedSourceOwner selected source.context)
      (site : GeneratedScalarSite (.compare operation a b) cfg.mod source.rootsEnv.access cx.fn
        (lowerEnv cfg.mod env.vars results) root source.path before required runtime.point)
      (coverage : map.Covers required)
      (admitted : map.Admitted cfg.mod.profile source.context.retained)
      (bounded : map.Bounded (lowerExpr b (lowerEnv cfg.mod env.vars results)
        (lowerExpr a (lowerEnv cfg.mod env.vars results) before).2).2.vals.size)
      (same : Same before.vals.size initial runtime.frame)
      (demanded : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs runtime) :
      GeneratedExpressionPrefixCompareCursor cx results selected leftCursor rightCursor source before
        (lowerExpr (.cmp operation a b) (lowerEnv cfg.mod env.vars results) before).2 initial start map required runtime

namespace GeneratedExpressionPrefixCompareCursor

variable {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
  {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
  {leftCursor rightCursor : ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
    LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
  {expression : Expr} {state : St} {source : ExprSource cfg env expression state}
  {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}

theorem canonical
    (leftDemand : ∀ {expression : Expr} {state : St} (child : ExprSource cfg env expression state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      leftCursor child before built initial start map required runtime → CanonicalExpressionDemand map cx child runtime)
    (rightDemand : ∀ {expression : Expr} {state : St} (child : ExprSource cfg env expression state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      rightCursor child before built initial start map required runtime → CanonicalExpressionDemand map cx child runtime)
    (cursor : GeneratedExpressionPrefixCompareCursor cx results selected leftCursor rightCursor source before built initial start map required runtime) :
    CanonicalExpressionDemand map cx source runtime := by
  cases cursor with
  | left child metadata owned occurrence rows coverage demanded => exact .child metadata (leftDemand child demanded)
  | right child metadata owned occurrence rows coverage leftPost demanded => exact .child metadata (rightDemand child demanded)
  | operation child metadata owned site coverage admitted bounded same demanded => exact .child metadata (.exit demanded)

theorem same
    (leftSame : ∀ {expression : Expr} {state : St} (child : ExprSource cfg env expression state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      leftCursor child before built initial start map required runtime → Same before.vals.size initial runtime.frame)
    (rightSame : ∀ {expression : Expr} {state : St} (child : ExprSource cfg env expression state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      rightCursor child before built initial start map required runtime → Same before.vals.size initial runtime.frame)
    (cursor : GeneratedExpressionPrefixCompareCursor cx results selected leftCursor rightCursor source before built initial start map required runtime) :
    Same before.vals.size initial runtime.frame := by
  cases cursor with
  | left child metadata owned occurrence rows coverage demanded => exact leftSame child demanded
  | right child metadata owned occurrence rows coverage leftPost demanded =>
    obtain ⟨_, post⟩ := leftPost
    exact post.same.trans (rightSame child demanded) post.mono
  | operation child metadata owned site coverage admitted bounded same demanded => exact same

#print axioms GeneratedExpressionPrefixCompareCursor.same

theorem realizes
    (leftDemand : ∀ {expression : Expr} {state : St} (child : ExprSource cfg env expression state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      leftCursor child before built initial start map required runtime → CanonicalExpressionDemand map cx child runtime)
    (rightDemand : ∀ {expression : Expr} {state : St} (child : ExprSource cfg env expression state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      rightCursor child before built initial start map required runtime → CanonicalExpressionDemand map cx child runtime)
    (cursor : GeneratedExpressionPrefixCompareCursor cx results selected leftCursor rightCursor source before built initial start map required runtime) :
    map.Realizes cfg.mod source.world env runtime := (cursor.canonical leftDemand rightDemand).carried

end GeneratedExpressionPrefixCompareCursor

theorem accepted_generated_compare_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (operation : CmpOp) (a b : Expr)
    (leftCursor rightCursor : ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (leftFamily : GeneratedExpressionPrefixFamily cx results selected loop a leftCursor)
    (rightFamily : GeneratedExpressionPrefixFamily cx results selected loop b rightCursor) :
    GeneratedExpressionPrefixFamily cx results selected loop (.cmp operation a b)
      (@GeneratedExpressionPrefixCompareCursor cfg env cx results root owner selected leftCursor rightCursor) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
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
    leftRealized leftInput leftExtended steps
  refine ⟨owned, coverage, ?_⟩
  cases leftDecomposed.progress with
  | interior demanded =>
    exact .interior (.left left leftMetadata leftOwned leftOccurrence leftRows coverage demanded)
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
      rightRealized rightInput rightExtended residual
    cases rightDecomposed.progress with
    | interior demanded =>
      exact .interior (.right right rightMetadata rightOwned rightOccurrence rightRows coverage ⟨_, leftBoundary.post⟩ demanded)
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
      · exact .interior (.operation right rightMetadata owned site coverage admitted rightBoundary.bounded combinedPost.same rightBoundary.demanded)
      · obtain ⟨_, _, _, _, _, _, value, _, _, _, _, done, finalBoundary⟩ :=
          accepted_generated_scalar_runtime_step (.compare operation a b) inputs source evaluated
            site coverage combinedPost rightBoundary.bounded currentRealized actual
        exact .complete (by omega) ((leftTrace.append rightTrace).append (.next actual (.zero _))) tail done finalBoundary

theorem accepted_generated_compare_literal_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (operation : CmpOp) (type : IntTy) (left right : Int) :
    GeneratedExpressionPrefixFamily cx results selected loop (.cmp operation (.lit type left) (.lit type right))
      (@GeneratedExpressionPrefixCompareCursor cfg env cx results root owner selected
        (@GeneratedExpressionPrefixLeafCursor cfg env cx results root owner selected)
        (@GeneratedExpressionPrefixLeafCursor cfg env cx results root owner selected)) :=
  accepted_generated_compare_prefix_family selected loop operation (.lit type left) (.lit type right) _ _
    (accepted_generated_literal_prefix_family selected loop type left)
    (accepted_generated_literal_prefix_family selected loop type right)

theorem accepted_generated_compare_boolean_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (operation : CmpOp) (left right : Bool) :
    GeneratedExpressionPrefixFamily cx results selected loop (.cmp operation (.bool left) (.bool right))
      (@GeneratedExpressionPrefixCompareCursor cfg env cx results root owner selected
        (@GeneratedExpressionPrefixLeafCursor cfg env cx results root owner selected)
        (@GeneratedExpressionPrefixLeafCursor cfg env cx results root owner selected)) :=
  accepted_generated_compare_prefix_family selected loop operation (.bool left) (.bool right) _ _
    (accepted_generated_boolean_prefix_family selected loop left)
    (accepted_generated_boolean_prefix_family selected loop right)

#print axioms accepted_generated_compare_prefix_family
#print axioms accepted_generated_compare_literal_prefix_family
#print axioms accepted_generated_compare_boolean_prefix_family

end Goose.Lower
