import Goose.Lower.DemandGeneratedExpressionPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive GeneratedExpressionStatementPrefixCursor {cfg : Cfg} {env : Env}
    (cursor : ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | expression {expression : Expr} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.expr expression origin) state} {child : ExprSource cfg env expression state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (canonical : source.ExpressionChildAt child rfl)
      (demanded : cursor child before built initial start map required runtime) :
      GeneratedExpressionStatementPrefixCursor (@cursor) source before built initial start map required runtime

theorem accepted_generated_expression_statement_prefix {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (expression : Expr) (origin : OriginId)
    (cursor : ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (childFamily : GeneratedExpressionPrefixFamily cx results selected loop expression (@cursor)) :
    GeneratedStatementPrefixFamily cx results selected loop (.expr expression origin)
      (@GeneratedExpressionStatementPrefixCursor cfg env (@cursor)) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  obtain ⟨child, typing, roots, canonical⟩ := source.exprChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.expression expression) before := by
    rw [canonical.path]
    exact .first occurrence (.discard loop expression origin)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.first occurrence (.discard loop expression origin)) required := .first (first := .discard loop expression origin) rows
    simpa only [roots, canonical.path] using inherited
  have childOwner : GeneratedSourceOwner selected child.context :=
    (owned.child rfl 0 (.expression expression) .expression rfl (by trivial)).transport
      canonical.plans.symm canonical.path.symm rfl canonical.context.symm
  have childAdmitted : map.Admitted cfg.mod.profile child.context.retained := by
    rw [demandContextRetainedEq canonical.plans canonical.path rfl canonical.context]
    intro profile alias member
    exact source.context.child_retained_subset rfl 0 (.expression expression) .expression rfl (by trivial)
      (admitted profile alias member)
  have childRealized : map.Realizes cfg.mod child.world env ⟨start, initial, state⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using realized
  have childInput : GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv before initial start := by
    rw [typing, roots]
    exact input
  have lowered : (lowerStmt loop (.expr expression origin) (lowerEnv cfg.mod env.vars results) before).2 =
      (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2 := by
    simp only [lowerStmt, bind_run, pure_run]
  have childExtended := extended
  rw [lowered] at childExtended
  have childProgress := childFamily child childOwner childOccurrence childRows coverage childAdmitted bounded
    childRealized childInput childExtended steps
  refine ⟨owned, coverage, ?_⟩
  cases childProgress.progress with
  | interior demanded =>
    apply DemandPrefixDecomposition.interior
    rw [lowered]
    exact .expression canonical demanded
  | @complete sourceFuel consumed remaining boundary value count prefixSteps residual evaluated finished =>
    have raw : execStmt (sourceFuel + 1) cfg env (.expr expression origin) state = .ok (.normal .unit) boundary.state := by
      simp only [execStmt, bind_apply, evaluated, pure_apply]
    have prepared : (execStmt (sourceFuel + 1) cfg env (.expr expression origin) >>= prepareLoopFlow env loop) state =
        .ok (.normal .unit) boundary.state := by
      simp only [bind_apply, raw]
      cases loop <;> rfl
    have carried : map.Realizes cfg.mod source.world env boundary := by
      simpa only [RetainedSsaMap.Realizes, canonical.world] using finished.demanded.operands
    exact .complete count prefixSteps residual prepared
      (.normal (by rw [lowered]; exact Post.nil finished.post.pp finished.post.mono finished.post.same finished.post.rel)
        (source.result (sourceFuel + 1) (.normal .unit) raw) (by rw [lowered]; exact finished.bounded) carried)

theorem GeneratedExpressionStatementPrefixCursor.leaf_frame {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (demanded : GeneratedExpressionStatementPrefixCursor
      (@GeneratedExpressionPrefixLeafCursor cfg env cx results root owner selected)
      source before built initial start map required runtime) :
    ∃ typing roots future, DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime := by
  cases demanded with
  | expression canonical demanded =>
    exact ⟨_, _, _, by simpa only [canonical.world] using demanded.frame⟩

end Goose.Lower
