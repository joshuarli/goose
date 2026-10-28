import Goose.Lower.DemandExpressionStatementEntry
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
  obtain ⟨child, typing, roots, canonical, childOccurrence, childRows, childOwner, childAdmitted,
    childRealized, childInput, childExtended, lowered⟩ :=
    accepted_generated_expression_statement_entry source selected owned occurrence rows admitted realized input extended
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
