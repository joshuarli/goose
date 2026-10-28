import Goose.Lower.DemandUnaryStoppedPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive StoppedExpressionPrefix {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    (source : ExprSource cfg env expression state) (map : RetainedSsaMap) (cx : FnCtx) (results : List Ty)
    (before : LS) (initial : GIR.Frame) (start : Pt) (taken : Nat) (reached : DemandRuntimePoint)
    (stop : Stop) (after : St) : Prop
  | aborted (fuel : Nat) (evaluated : evalExpr fuel cfg env expression state = .stop stop after) :
      StoppedExpressionPrefix source map cx results before initial start taken reached stop after
  | complete {fuel consumed remaining : Nat} {boundary : DemandRuntimePoint} {value : Val}
      (count : consumed + remaining = taken)
      (executed : DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ boundary)
      (residual : DemandRuntimePrefix cx remaining boundary reached)
      (evaluated : evalExpr fuel cfg env expression state = .ok value boundary.state)
      (post : GeneratedExpressionPrefixEnd source map cx before initial
        (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2
        (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).1 value boundary) :
      StoppedExpressionPrefix source map cx results before initial start taken reached stop after

def GeneratedStoppedExpressionPrefixFamily {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (expression : Expr) : Prop :=
  ∀ {state : St} (source : ExprSource cfg env expression state) {before : LS}
    (_owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression expression) before)
    {required map : RetainedSsaMap} (_rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required),
    map.Covers required → map.Admitted cfg.mod.profile source.context.retained → map.Bounded before.vals.size →
    ∀ {initial : GIR.Frame} {start : Pt}, map.Realizes cfg.mod source.world env ⟨start, initial, state⟩ →
    GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start →
    ExtT (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks →
    ∀ {taken : Nat} {reached : DemandRuntimePoint}, DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached →
    ∀ {fuel : Nat} {stop : Stop} {after : St}, DemandInstructionStop cx fuel reached stop after → stop ≠ .timeout →
    StoppedExpressionPrefix source map cx results before initial start taken reached stop after

theorem GeneratedExpressionPrefixLeafCursor.excludes_stop {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {expression : Expr} {state : St} {source : ExprSource cfg env expression state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : GeneratedExpressionPrefixLeafCursor cx results selected source before built initial start map required runtime)
    {fuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx fuel runtime stop after) (nonTimeout : stop ≠ .timeout) : False := by
  obtain ⟨form, entry, site⟩ := cursor.site
  cases stopped with
  | timeout => exact nonTimeout rfl
  | definition instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    cases form <;> simp_all [ScalarExpression.boundary, ScalarExpression.operation, execOp, execPure, pure_apply]
  | effect instruction execution => cases site.instruction.symm.trans instruction

theorem accepted_generated_leaf_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {expression : Expr} (form : ScalarExpression expression)
    (entry : form.boundary = .entry) (inputs : form.Inputs) :
    GeneratedStoppedExpressionPrefixFamily cx results selected loop expression := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
  have decomposition := accepted_generated_expression_leaf_prefix form entry inputs source selected owned occurrence rows
    coverage admitted bounded realized input.atPoint input.related extended steps
  cases decomposition.progress with
  | interior cursor => exact (cursor.excludes_stop stopped nonTimeout).elim
  | complete count prefixSteps residual evaluated post => exact .complete count prefixSteps residual evaluated post

#print axioms accepted_generated_leaf_stopped_family

theorem accepted_generated_unary_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (operation : UnOp) (expression : Expr) (origin : OriginId)
    (childFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop expression)
    {state : St} (source : ExprSource cfg env (.un operation expression origin) state) {before : LS}
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.un operation expression origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (.un operation expression origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    StoppedExpressionPrefix source map cx results before initial start taken reached stop after := by
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨child, typing, roots, intType, type, metadata⟩ := source.unChild operation origin
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
    have emitted : ExtT (emitDef ((ScalarExpression.unary operation expression origin).operation le before) le
        ((ScalarExpression.unary operation expression origin).prefix le before)).2 cx.fn.blocks := by
      simpa only [(ScalarExpression.unary operation expression origin).lower] using extended
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
    obtain ⟨number, rfl⟩ := hasTy_int typed
    have site : GeneratedScalarSite (.unary operation expression origin) cfg.mod source.rootsEnv.access cx.fn le
        root source.path before required boundary.point :=
      ⟨occurrence, .first (first := .expression rfl) rows, completed.post.pp, extended⟩
    have currentRealized : map.Realizes cfg.mod source.world env boundary := by
      simpa only [RetainedSsaMap.Realizes, metadata.world] using completed.demanded.operands
    rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨rest, current, rfl, actual, tail⟩
    · obtain ⟨_, _, _, _, done, _, _⟩ := accepted_generated_scalar_runtime_stop
        (.unary operation expression origin) (intType, number) source evaluated site coverage completed.post
        currentRealized stopped nonTimeout
      exact .aborted (fuel + 1) done
    · obtain ⟨_, _, _, _, _, _, result, _, _, _, _, done, final⟩ :=
        accepted_generated_scalar_runtime_step (.unary operation expression origin) (intType, number) source evaluated site coverage
          completed.post completed.bounded currentRealized actual
      exact .complete (by omega) (childTrace.append (.next actual (.zero _))) tail done final

theorem accepted_generated_convert_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (kind : ConvKind) (target : IntTy) (expression : Expr) (origin : OriginId)
    (childFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop expression)
    {state : St} (source : ExprSource cfg env (.conv kind (.int target) expression origin) state) {before : LS}
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.conv kind (.int target) expression origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerExpr (.conv kind (.int target) expression origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    StoppedExpressionPrefix source map cx results before initial start taken reached stop after := by
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨child, typing, roots, intType, targetType, type, targetEq, metadata⟩ := source.convChild kind (.int target) origin
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
    have emitted : ExtT (emitDef ((ScalarExpression.convert kind target expression origin).operation le before) le
        ((ScalarExpression.convert kind target expression origin).prefix le before)).2 cx.fn.blocks := by
      simpa only [(ScalarExpression.convert kind target expression origin).lower] using extended
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
    obtain ⟨number, rfl⟩ := hasTy_int typed
    have site : GeneratedScalarSite (.convert kind target expression origin) cfg.mod source.rootsEnv.access cx.fn le
        root source.path before required boundary.point :=
      ⟨occurrence, .first (first := .expression rfl) rows, completed.post.pp, extended⟩
    have currentRealized : map.Realizes cfg.mod source.world env boundary := by
      simpa only [RetainedSsaMap.Realizes, metadata.world] using completed.demanded.operands
    rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨rest, current, rfl, actual, tail⟩
    · obtain ⟨_, _, _, _, done, _, _⟩ := accepted_generated_scalar_runtime_stop
        (.convert kind target expression origin) (intType, number) source evaluated site coverage completed.post
        currentRealized stopped nonTimeout
      exact .aborted (fuel + 1) done
    · obtain ⟨_, _, _, _, _, _, result, _, _, _, _, done, final⟩ :=
        accepted_generated_scalar_runtime_step (.convert kind target expression origin) (intType, number) source evaluated site coverage
          completed.post completed.bounded currentRealized actual
      exact .complete (by omega) (childTrace.append (.next actual (.zero _))) tail done final

inductive UnaryStoppedExpression : Expr → Prop
  | literal (type : IntTy) (number : Int) : UnaryStoppedExpression (.lit type number)
  | boolean (value : Bool) : UnaryStoppedExpression (.bool value)
  | unary (operation : UnOp) {expression : Expr} (origin : OriginId) (child : UnaryStoppedExpression expression) :
      UnaryStoppedExpression (.un operation expression origin)
  | convert (kind : ConvKind) (target : IntTy) {expression : Expr} (origin : OriginId) (child : UnaryStoppedExpression expression) :
      UnaryStoppedExpression (.conv kind (.int target) expression origin)

theorem accepted_generated_unary_stopped_expressions {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {expression : Expr} (form : UnaryStoppedExpression expression) :
    GeneratedStoppedExpressionPrefixFamily cx results selected loop expression := by
  induction form with
  | literal type number => exact accepted_generated_leaf_stopped_family selected loop (.literal type number) rfl ()
  | boolean value => exact accepted_generated_leaf_stopped_family selected loop (.boolean value) rfl ()
  | unary operation origin child ih => exact accepted_generated_unary_stopped_family selected loop operation _ origin ih
  | convert kind target origin child ih => exact accepted_generated_convert_stopped_family selected loop kind target _ origin ih

#print axioms accepted_generated_unary_stopped_expressions
#print axioms accepted_generated_convert_stopped_family
#print axioms accepted_generated_unary_stopped_family

end Goose.Lower
