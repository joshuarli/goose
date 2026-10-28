import Goose.Lower.DemandStoppedExpressionFamily

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem accepted_generated_binary_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (operation : BinOp) (a b : Expr) (origin : OriginId)
    (leftFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop a)
    (rightFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop b) :
    GeneratedStoppedExpressionPrefixFamily cx results selected loop (.bin operation a b origin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
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
    leftRealized leftInput leftExtended steps stopped nonTimeout
  cases leftDecomposed with
  | aborted fuel done =>
    apply StoppedExpressionPrefix.aborted (fuel + 1)
    simp [evalExpr, bind_apply, done]
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
      rightRealized rightInput rightExtended residual stopped nonTimeout
    cases rightDecomposed with
    | aborted rightFuel rightStopped =>
      let common := max leftFuel rightFuel
      have leftDone' : evalExpr common cfg env a state = .ok (.int intType leftNumber) middle.state :=
        ((monoAll leftFuel common (by dsimp [common]; exact Nat.le_max_left _ _)).expr cfg env a state).1 _ _ leftDone
      have rightDone' : evalExpr common cfg env b middle.state = .stop stop after := by
        rcases ((monoAll rightFuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env b middle.state).2 _ _ rightStopped with timeout | done
        · cases stop <;> simp_all [Goose.Proofs.Fuel.isTimeout]
        · exact done
      apply StoppedExpressionPrefix.aborted (common + 1)
      simp [evalExpr, bind_apply, leftDone', rightDone', Core.expectInt, pure_apply]
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
      · obtain ⟨_, _, _, _, done, _, _⟩ := accepted_generated_scalar_runtime_stop
          (.binary operation a b origin) (intType, leftNumber, rightNumber) source evaluated site coverage combinedPost
          currentRealized stopped nonTimeout
        exact .aborted (sourceFuel + 1) done
      · obtain ⟨_, _, _, _, _, _, value, _, _, _, _, done, finalBoundary⟩ :=
          accepted_generated_scalar_runtime_step (.binary operation a b origin) (intType, leftNumber, rightNumber) source evaluated
            site coverage combinedPost rightBoundary.bounded currentRealized actual
        exact .complete (by omega) ((leftTrace.append rightTrace).append (.next actual (.zero _))) tail done finalBoundary

theorem accepted_generated_not_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (expression : Expr)
    (childFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop expression)
    {state : St} (source : ExprSource cfg env (.not expression) state) {before : LS}
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.not expression)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (.not expression) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    StoppedExpressionPrefix source map cx results before initial start taken reached stop after := by
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨child, typing, roots, type, metadata⟩ := source.notChild
  have childOwned : GeneratedSourceOwner selected child.context :=
    (owned.child rfl 0 (.expression expression) .expression rfl (by trivial)).transport
      metadata.plans.symm metadata.path.symm rfl metadata.context.symm
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.expression expression) before := by
    rw [metadata.path]
    exact .first occurrence (.expression rfl)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access
        (.first occurrence (.expression rfl)) required := .first (first := .expression rfl) rows
    simpa only [roots, metadata.path] using inherited
  have childAdmitted : map.Admitted cfg.mod.profile child.context.retained := by
    intro profile alias member
    exact metadata.retained alias (admitted profile alias member)
  have childRealized : map.Realizes cfg.mod child.world env ⟨start, initial, state⟩ := by
    simpa only [metadata.world] using realized
  have childInput : GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv before initial start := by
    simpa only [typing, roots] using input
  have childExtended : ExtT (lowerExpr expression le before).2 cx.fn.blocks := by
    have emitted : ExtT (emitDef ((ScalarExpression.negate expression).operation le before) le
        ((ScalarExpression.negate expression).prefix le before)).2 cx.fn.blocks := by
      simpa only [(ScalarExpression.negate expression).lower] using extended
    exact emitted.of_adv (adv_emitDef rfl)
  have decomposition := childFamily child childOwned childOccurrence childRows coverage childAdmitted bounded
    childRealized childInput childExtended steps stopped nonTimeout
  cases decomposition with
  | aborted childFuel childStopped =>
    apply StoppedExpressionPrefix.aborted (childFuel + 1)
    simp [evalExpr, bind_apply, childStopped]
  | @complete fuel consumed remaining boundary value count childTrace residual evaluated completed =>
    have typed := (child.result fuel value evaluated).typed
    rw [type] at typed
    obtain ⟨boolean, rfl⟩ := hasTy_bool typed
    have site : GeneratedScalarSite (.negate expression) cfg.mod source.rootsEnv.access cx.fn le
        root source.path before required boundary.point :=
      ⟨occurrence, .first (first := .expression rfl) rows, completed.post.pp, extended⟩
    have currentRealized : map.Realizes cfg.mod source.world env boundary := by
      simpa only [RetainedSsaMap.Realizes, metadata.world] using completed.demanded.operands
    rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨rest, current, rfl, actual, tail⟩
    · obtain ⟨_, _, _, _, done, _, _⟩ := accepted_generated_scalar_runtime_stop
        (.negate expression) boolean source evaluated site coverage completed.post
        currentRealized stopped nonTimeout
      exact .aborted (fuel + 1) done
    · obtain ⟨_, _, _, _, _, _, result, _, _, _, _, done, final⟩ :=
        accepted_generated_scalar_runtime_step (.negate expression) boolean source evaluated site coverage
          completed.post completed.bounded currentRealized actual
      exact .complete (by omega) (childTrace.append (.next actual (.zero _))) tail done final

inductive NumericStoppedExpression : Expr → Prop
  | unary {expression : Expr} (form : UnaryStoppedExpression expression) : NumericStoppedExpression expression
  | not {expression : Expr} (child : NumericStoppedExpression expression) : NumericStoppedExpression (.not expression)
  | unaryOperation (operation : UnOp) {expression : Expr} (origin : OriginId) (child : NumericStoppedExpression expression) :
      NumericStoppedExpression (.un operation expression origin)
  | convert (kind : ConvKind) (target : IntTy) {expression : Expr} (origin : OriginId) (child : NumericStoppedExpression expression) :
      NumericStoppedExpression (.conv kind (.int target) expression origin)
  | binary (operation : BinOp) {left right : Expr} (origin : OriginId)
      (first : NumericStoppedExpression left) (second : NumericStoppedExpression right) :
      NumericStoppedExpression (.bin operation left right origin)

theorem accepted_generated_numeric_stopped_expressions {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {expression : Expr} (form : NumericStoppedExpression expression) :
    GeneratedStoppedExpressionPrefixFamily cx results selected loop expression := by
  induction form with
  | unary form => exact accepted_generated_unary_stopped_expressions selected loop form
  | not child ih => exact accepted_generated_not_stopped_family selected loop _ ih
  | unaryOperation operation origin child ih => exact accepted_generated_unary_stopped_family selected loop operation _ origin ih
  | convert kind target origin child ih => exact accepted_generated_convert_stopped_family selected loop kind target _ origin ih
  | binary operation origin first second firstIH secondIH =>
    exact accepted_generated_binary_stopped_family selected loop operation _ _ origin firstIH secondIH

#print axioms accepted_generated_not_stopped_family
#print axioms accepted_generated_numeric_stopped_expressions
#print axioms accepted_generated_binary_stopped_family

end Goose.Lower
