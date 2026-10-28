import Goose.Lower.DemandStoppedExpressionFamily
import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem GeneratedExpressionPrefixDecomposition.reachable {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    {source : ExprSource cfg env expression state} {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression expression) before}
    {required : RetainedSsaMap} {rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required}
    {map : RetainedSsaMap} {initial : GIR.Frame} {start : Pt} {cursor : DemandRuntimePoint → Prop}
    {taken : Nat} {reached : DemandRuntimePoint}
    (decomposition : GeneratedExpressionPrefixDecomposition (cx := cx) (results := results)
      source selected occurrence rows map initial start cursor taken reached)
    (callerStart : RuntimePoint cx.cfg cx.fn start initial state)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedExpressionPrefixDecomposition (cx := cx) (results := results) source selected occurrence rows map initial start
      (fun point => cursor point ∧ RuntimePoint cx.cfg cx.fn point.point point.frame point.state) taken reached := by
  refine ⟨decomposition.sourceOwner, decomposition.coverage, ?_⟩
  cases decomposition.progress with
  | interior current => exact .interior ⟨current, steps.reachable callerStart⟩
  | complete count executed residual evaluated result => exact .complete count executed residual evaluated result

theorem StoppedExpressionPrefix.reachable {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    {source : ExprSource cfg env expression state} {map : RetainedSsaMap} {cx : FnCtx} {results : List Ty}
    {before : LS} {initial : GIR.Frame} {start : Pt} {taken : Nat} {reached : DemandRuntimePoint}
    {stop : Stop} {after : St}
    (outcome : StoppedExpressionPrefix source map cx results before initial start taken reached stop after)
    (callerStart : RuntimePoint cx.cfg cx.fn start initial state)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    StoppedExpressionPrefix source map cx results before initial start taken reached stop after ∧
      RuntimePoint cx.cfg cx.fn reached.point reached.frame reached.state :=
  ⟨outcome, steps.reachable callerStart⟩

#print axioms GeneratedExpressionPrefixDecomposition.reachable
#print axioms StoppedExpressionPrefix.reachable
end Goose.Lower
