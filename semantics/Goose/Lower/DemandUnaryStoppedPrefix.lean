import Goose.Lower.DemandShortCircuitPrefixFamily

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive UnaryStoppedPrefix {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    (source : ExprSource cfg env expression state) (map : RetainedSsaMap) (cx : FnCtx)
    (before : LS) (initial : GIR.Frame) (start : Pt) (taken : Nat) (reached : DemandRuntimePoint)
    (stop : Stop) (after : St) : Prop
  | interior (cursor : CanonicalExpressionDemand map cx source reached) :
      UnaryStoppedPrefix source map cx before initial start taken reached stop after
  | aborted (fuel : Nat) (evaluated : evalExpr fuel cfg env expression state = .stop stop after)
      (cursor : CanonicalExpressionDemand map cx source reached) :
      UnaryStoppedPrefix source map cx before initial start taken reached stop after
  | complete {fuel consumed remaining : Nat} {boundary : DemandRuntimePoint} {value : Val}
      (count : consumed + remaining = taken)
      (executed : DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ boundary)
      (residual : DemandRuntimePrefix cx remaining boundary reached)
      (evaluated : evalExpr fuel cfg env expression state = .ok value boundary.state)
      (post : GeneratedExpressionPrefixEnd source map cx before initial
        (lowerExpr expression (lowerEnv cfg.mod env.vars cx.fn.results) before).2
        (lowerExpr expression (lowerEnv cfg.mod env.vars cx.fn.results) before).1 value boundary) :
      UnaryStoppedPrefix source map cx before initial start taken reached stop after

theorem accepted_generated_unary_stopped_prefix {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (operation : UnOp) (expression : Expr) (origin : OriginId)
    (childFamily : GeneratedExpressionPrefixFamily cx results selected loop expression (@CanonicalExpressionPrefixCursor cfg env cx))
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
    UnaryStoppedPrefix source map cx before initial start taken reached stop after := by
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
    childRealized childInput childExtended steps
  cases decomposition.progress with
  | interior demanded => exact .interior (.child metadata demanded)
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
      exact .aborted (fuel + 1) done (.child metadata (.exit completed.demanded))
    · obtain ⟨_, _, _, _, _, _, result, _, _, _, _, done, final⟩ :=
        accepted_generated_scalar_runtime_step (.unary operation expression origin) (intType, number) source evaluated site coverage
          completed.post completed.bounded currentRealized actual
      have final' : GeneratedExpressionPrefixEnd source map cx before initial
          (lowerExpr (.un operation expression origin) (lowerEnv cfg.mod env.vars cx.fn.results) before).2
          (lowerExpr (.un operation expression origin) (lowerEnv cfg.mod env.vars cx.fn.results) before).1 result current := by
        rw [input.resultsEq]
        exact final
      exact .complete (by omega) (childTrace.append (.next actual (.zero _))) tail done final'

#print axioms accepted_generated_unary_stopped_prefix

end Goose.Lower
