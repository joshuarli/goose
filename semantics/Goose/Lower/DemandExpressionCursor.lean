import Goose.Lower.DemandExpressionResult
import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive CanonicalExpressionDemand {cfg : Cfg} {env : Env} (map : RetainedSsaMap) (cx : FnCtx) :
    {expression : Expr} → {state : St} → ExprSource cfg env expression state → DemandRuntimePoint → Prop
  | entry {expression : Expr} {state : St} {source : ExprSource cfg env expression state}
      {runtime : DemandRuntimePoint}
      (demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
        source.context.inputFuture map.values map.runs runtime) :
      CanonicalExpressionDemand map cx source runtime
  | exit {expression : Expr} {state : St} {source : ExprSource cfg env expression state}
      {runtime : DemandRuntimePoint}
      (demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
        source.context.outputFuture map.values map.runs runtime) :
      CanonicalExpressionDemand map cx source runtime
  | child {expression childExpression : Expr} {state childState : St}
      {source : ExprSource cfg env expression state} {child : ExprSource cfg env childExpression childState}
      {index : Nat} {found : DemandNode.child? (.expression expression) index = some (.expression childExpression)}
      {runtime : DemandRuntimePoint} (metadata : source.ChildAt child index found)
      (demanded : CanonicalExpressionDemand map cx child runtime) :
      CanonicalExpressionDemand map cx source runtime

theorem CanonicalExpressionDemand.carried {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    {source : ExprSource cfg env expression state} {map : RetainedSsaMap} {cx : FnCtx}
    {runtime : DemandRuntimePoint} (cursor : CanonicalExpressionDemand map cx source runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  induction cursor with
  | entry demanded => exact demanded.operands
  | exit demanded => exact demanded.operands
  | child metadata demanded induction => simpa only [metadata.world] using induction

end Goose.Lower
