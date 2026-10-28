import Goose.Lower.DemandGeneratedExpressionPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive GeneratedExpressionPrefixConvertCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (childCursor : ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) :
    ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | child {kind : ConvKind} {target : IntTy} {origin : OriginId} {expression : Expr} {state : St} {source : ExprSource cfg env (.conv kind (.int target) expression origin) state}
      {before : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env expression state) (metadata : source.ChildAt child 0 rfl)
      (owned : GeneratedSourceOwner selected child.context)
      (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root child.path (.expression expression) before)
      (rows : GeneratedDemandRows cfg.mod child.rootsEnv.access occurrence required)
      (coverage : map.Covers required)
      (demanded : childCursor child before (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2
        initial start map required runtime) :
      GeneratedExpressionPrefixConvertCursor cx results selected childCursor source before
        (lowerExpr (.conv kind (.int target) expression origin) (lowerEnv cfg.mod env.vars results) before).2 initial start map required runtime
  | operation {kind : ConvKind} {target : IntTy} {origin : OriginId} {expression : Expr} {state : St} {source : ExprSource cfg env (.conv kind (.int target) expression origin) state}
      {before : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env expression state) (metadata : source.ChildAt child 0 rfl)
      (owned : GeneratedSourceOwner selected source.context)
      (site : GeneratedScalarSite (.convert kind target expression origin) cfg.mod source.rootsEnv.access cx.fn
        (lowerEnv cfg.mod env.vars results) root source.path before required runtime.point)
      (coverage : map.Covers required)
      (admitted : map.Admitted cfg.mod.profile source.context.retained)
      (bounded : map.Bounded (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2.vals.size)
      (same : Same before.vals.size initial runtime.frame)
      (demanded : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs runtime) :
      GeneratedExpressionPrefixConvertCursor cx results selected childCursor source before
        (lowerExpr (.conv kind (.int target) expression origin) (lowerEnv cfg.mod env.vars results) before).2 initial start map required runtime

namespace GeneratedExpressionPrefixConvertCursor

variable {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
  {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
  {childCursor : ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
    LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
  {expression : Expr} {state : St} {source : ExprSource cfg env expression state}
  {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}

theorem canonical
    (childDemand : ∀ {expression : Expr} {state : St} (child : ExprSource cfg env expression state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      childCursor child before built initial start map required runtime → CanonicalExpressionDemand map cx child runtime)
    (cursor : GeneratedExpressionPrefixConvertCursor cx results selected childCursor source before built initial start map required runtime) :
    CanonicalExpressionDemand map cx source runtime := by
  cases cursor with
  | child child metadata owned occurrence rows coverage demanded => exact .child metadata (childDemand child demanded)
  | operation child metadata owned site coverage admitted bounded same demanded => exact .child metadata (.exit demanded)


theorem same
    (childSame : ∀ {expression : Expr} {state : St} (child : ExprSource cfg env expression state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      childCursor child before built initial start map required runtime → Same before.vals.size initial runtime.frame)
    (cursor : GeneratedExpressionPrefixConvertCursor cx results selected childCursor source before built initial start map required runtime) :
    Same before.vals.size initial runtime.frame := by
  cases cursor with
  | child child metadata owned occurrence rows coverage demanded => exact childSame child demanded
  | operation child metadata owned site coverage admitted bounded same demanded => exact same

#print axioms GeneratedExpressionPrefixConvertCursor.same

theorem realizes
    (childDemand : ∀ {expression : Expr} {state : St} (child : ExprSource cfg env expression state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      childCursor child before built initial start map required runtime → CanonicalExpressionDemand map cx child runtime)
    (cursor : GeneratedExpressionPrefixConvertCursor cx results selected childCursor source before built initial start map required runtime) :
    map.Realizes cfg.mod source.world env runtime := (cursor.canonical childDemand).carried

end GeneratedExpressionPrefixConvertCursor

theorem accepted_generated_convert_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (kind : ConvKind) (target : IntTy) (expression : Expr) (origin : OriginId)
    (childCursor : ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (childFamily : GeneratedExpressionPrefixFamily cx results selected loop expression childCursor) :
    GeneratedExpressionPrefixFamily cx results selected loop (.conv kind (.int target) expression origin)
      (@GeneratedExpressionPrefixConvertCursor cfg env cx results root owner selected childCursor) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
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
  have decomposed := childFamily child childOwned childOccurrence childRows coverage childAdmitted bounded
    childRealized childInput childExtended steps
  refine ⟨owned, coverage, ?_⟩
  cases decomposed.progress with
  | interior demanded =>
    exact .interior (.child child metadata childOwned childOccurrence childRows coverage demanded)
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
    · exact .interior (.operation child metadata owned site coverage admitted completed.bounded completed.post.same completed.demanded)
    · obtain ⟨_, _, _, _, _, _, result, _, _, _, _, done, finalBoundary⟩ :=
        accepted_generated_scalar_runtime_step (.convert kind target expression origin) (intType, number) source evaluated site coverage
          completed.post completed.bounded currentRealized actual
      exact .complete (by omega) (childTrace.append (.next actual (.zero _))) tail done finalBoundary

theorem accepted_generated_convert_literal_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (kind : ConvKind) (target : IntTy) (type : IntTy) (number : Int) (origin : OriginId) :
    GeneratedExpressionPrefixFamily cx results selected loop (.conv kind (.int target) (.lit type number) origin)
      (@GeneratedExpressionPrefixConvertCursor cfg env cx results root owner selected
        (@GeneratedExpressionPrefixLeafCursor cfg env cx results root owner selected)) :=
  accepted_generated_convert_prefix_family selected loop kind target (.lit type number) origin _
    (accepted_generated_literal_prefix_family selected loop type number)

#print axioms accepted_generated_convert_prefix_family
#print axioms accepted_generated_convert_literal_prefix_family

end Goose.Lower
