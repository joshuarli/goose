import Goose.Lower.DemandGeneratedExpressionPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

inductive GeneratedExpressionPrefixBinaryCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (leftCursor rightCursor : ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) :
    ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | left {operation : BinOp} {origin : OriginId} {a b : Expr} {state : St}
      {source : ExprSource cfg env (.bin operation a b origin) state}
      {before : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env a state) (metadata : source.ChildAt child 0 rfl)
      (owned : GeneratedSourceOwner selected child.context)
      (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root child.path (.expression a) before)
      (rows : GeneratedDemandRows cfg.mod child.rootsEnv.access occurrence required)
      (coverage : map.Covers required)
      (demanded : leftCursor child before (lowerExpr a (lowerEnv cfg.mod env.vars results) before).2
        initial start map required runtime) :
      GeneratedExpressionPrefixBinaryCursor cx results selected leftCursor rightCursor source before
        (lowerExpr (.bin operation a b origin) (lowerEnv cfg.mod env.vars results) before).2 initial start map required runtime
  | right {operation : BinOp} {origin : OriginId} {a b : Expr} {state afterLeft : St}
      {source : ExprSource cfg env (.bin operation a b origin) state}
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
      GeneratedExpressionPrefixBinaryCursor cx results selected leftCursor rightCursor source before
        (lowerExpr (.bin operation a b origin) (lowerEnv cfg.mod env.vars results) before).2 initial start map required runtime
  | operation {operation : BinOp} {origin : OriginId} {a b : Expr} {state afterLeft : St}
      {source : ExprSource cfg env (.bin operation a b origin) state}
      {before : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env b afterLeft) (metadata : source.ChildAt child 1 rfl)
      (owned : GeneratedSourceOwner selected source.context)
      (site : GeneratedScalarSite (.binary operation a b origin) cfg.mod source.rootsEnv.access cx.fn
        (lowerEnv cfg.mod env.vars results) root source.path before required runtime.point)
      (coverage : map.Covers required)
      (admitted : map.Admitted cfg.mod.profile source.context.retained)
      (bounded : map.Bounded (lowerExpr b (lowerEnv cfg.mod env.vars results)
        (lowerExpr a (lowerEnv cfg.mod env.vars results) before).2).2.vals.size)
      (same : Same before.vals.size initial runtime.frame)
      (demanded : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs runtime) :
      GeneratedExpressionPrefixBinaryCursor cx results selected leftCursor rightCursor source before
        (lowerExpr (.bin operation a b origin) (lowerEnv cfg.mod env.vars results) before).2 initial start map required runtime

namespace GeneratedExpressionPrefixBinaryCursor

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
    (cursor : GeneratedExpressionPrefixBinaryCursor cx results selected leftCursor rightCursor source before built initial start map required runtime) :
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
    (cursor : GeneratedExpressionPrefixBinaryCursor cx results selected leftCursor rightCursor source before built initial start map required runtime) :
    Same before.vals.size initial runtime.frame := by
  cases cursor with
  | left child metadata owned occurrence rows coverage demanded => exact leftSame child demanded
  | right child metadata owned occurrence rows coverage leftPost demanded =>
    obtain ⟨_, post⟩ := leftPost
    exact post.same.trans (rightSame child demanded) post.mono
  | operation child metadata owned site coverage admitted bounded same demanded => exact same

#print axioms GeneratedExpressionPrefixBinaryCursor.same

theorem realizes
    (leftDemand : ∀ {expression : Expr} {state : St} (child : ExprSource cfg env expression state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      leftCursor child before built initial start map required runtime → CanonicalExpressionDemand map cx child runtime)
    (rightDemand : ∀ {expression : Expr} {state : St} (child : ExprSource cfg env expression state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      rightCursor child before built initial start map required runtime → CanonicalExpressionDemand map cx child runtime)
    (cursor : GeneratedExpressionPrefixBinaryCursor cx results selected leftCursor rightCursor source before built initial start map required runtime) :
    map.Realizes cfg.mod source.world env runtime := (cursor.canonical leftDemand rightDemand).carried

end GeneratedExpressionPrefixBinaryCursor

theorem accepted_generated_binary_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (operation : BinOp) (a b : Expr) (origin : OriginId)
    (leftCursor rightCursor : ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (leftFamily : GeneratedExpressionPrefixFamily cx results selected loop a leftCursor)
    (rightFamily : GeneratedExpressionPrefixFamily cx results selected loop b rightCursor) :
    GeneratedExpressionPrefixFamily cx results selected loop (.bin operation a b origin)
      (@GeneratedExpressionPrefixBinaryCursor cfg env cx results root owner selected leftCursor rightCursor) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨intType, left, leftTyping, leftRoots, leftType, leftMetadata, rightSource⟩ := source.binChildren operation origin
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
    have emitted : ExtT (emitDef ((ScalarExpression.binary operation a b origin).operation le before) le
        ((ScalarExpression.binary operation a b origin).prefix le before)).2 cx.fn.blocks := by
      simpa only [(ScalarExpression.binary operation a b origin).lower] using extended
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
    have typed := (left.result leftFuel leftValue leftDone).typed
    rw [leftType] at typed
    obtain ⟨leftNumber, rfl⟩ := hasTy_int typed
    obtain ⟨right, rightTyping, rightRoots, rightType, rightMetadata⟩ := rightSource leftFuel (.int intType leftNumber) middle.state leftDone
    have rightOwned : GeneratedSourceOwner selected right.context :=
      (owned.child rfl 1 (.expression b) .expression rfl (by trivial)).transport
        rightMetadata.plans.symm rightMetadata.path.symm rfl rightMetadata.context.symm
    have rightOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root right.path (.expression b) (lowerExpr a le before).2 := by
      rw [rightMetadata.path]
      exact .binaryRight occurrence
    have rightRows : GeneratedDemandRows cfg.mod right.rootsEnv.access rightOccurrence required := by
      have inherited := generated_scalar_binary_rows source occurrence rows
      simpa only [rightRoots, rightMetadata.path, ScalarExpression.ownerOccurrence, ScalarExpression.ownerPath,
        ScalarExpression.ownerExpression, ScalarExpression.ownerBefore] using inherited
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
      have typed := (right.result rightFuel rightValue rightDone).typed
      rw [rightType] at typed
      obtain ⟨rightNumber, rfl⟩ := hasTy_int typed
      have post := leftBoundary.post.comp rightBoundary.post
      have combinedPost : Post cfg env cx before initial ((ScalarExpression.binary operation a b origin).prefix le before)
          boundary.frame boundary.point ((ScalarExpression.binary operation a b origin).cells le before (intType, leftNumber, rightNumber)) := by
        simpa only [ScalarExpression.prefix, ScalarExpression.cells, List.singleton_append] using post
      let sourceFuel := max leftFuel rightFuel
      have leftDone' : evalExpr sourceFuel cfg env a state = .ok (.int intType leftNumber) middle.state :=
        ((monoAll leftFuel sourceFuel (by dsimp only [sourceFuel]; exact Nat.le_max_left _ _)).expr cfg env a state).1 _ _ leftDone
      have rightDone' : evalExpr sourceFuel cfg env b middle.state = .ok (.int intType rightNumber) boundary.state :=
        ((monoAll rightFuel sourceFuel (by dsimp only [sourceFuel]; exact Nat.le_max_right _ _)).expr cfg env b middle.state).1 _ _ rightDone
      have evaluated : (ScalarExpression.binary operation a b origin).PrefixEvaluated (intType, leftNumber, rightNumber)
          sourceFuel cfg env state boundary.state := ⟨middle.state, leftDone', rightDone'⟩
      have site : GeneratedScalarSite (.binary operation a b origin) cfg.mod source.rootsEnv.access cx.fn le
          root source.path before required boundary.point :=
        ⟨occurrence, generated_scalar_binary_rows source occurrence rows, combinedPost.pp, extended⟩
      have currentRealized : map.Realizes cfg.mod source.world env boundary := by
        simpa only [RetainedSsaMap.Realizes, rightMetadata.world] using rightBoundary.demanded.operands
      rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨rest, current, rfl, actual, tail⟩
      · exact .interior (.operation right rightMetadata owned site coverage admitted rightBoundary.bounded combinedPost.same rightBoundary.demanded)
      · obtain ⟨_, _, _, _, _, _, value, _, _, _, _, done, finalBoundary⟩ :=
          accepted_generated_scalar_runtime_step (.binary operation a b origin) (intType, leftNumber, rightNumber) source evaluated
            site coverage combinedPost rightBoundary.bounded currentRealized actual
        exact .complete (by omega) ((leftTrace.append rightTrace).append (.next actual (.zero _))) tail done finalBoundary

theorem accepted_generated_binary_literal_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (operation : BinOp) (type : IntTy) (left right : Int) (origin : OriginId) :
    GeneratedExpressionPrefixFamily cx results selected loop (.bin operation (.lit type left) (.lit type right) origin)
      (@GeneratedExpressionPrefixBinaryCursor cfg env cx results root owner selected
        (@GeneratedExpressionPrefixLeafCursor cfg env cx results root owner selected)
        (@GeneratedExpressionPrefixLeafCursor cfg env cx results root owner selected)) :=
  accepted_generated_binary_prefix_family selected loop operation (.lit type left) (.lit type right) origin _ _
    (accepted_generated_literal_prefix_family selected loop type left)
    (accepted_generated_literal_prefix_family selected loop type right)

#print axioms accepted_generated_binary_prefix_family
#print axioms accepted_generated_binary_literal_prefix_family

end Goose.Lower
