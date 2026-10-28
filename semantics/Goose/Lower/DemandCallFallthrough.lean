import Goose.Lower.DemandCallNormalReturn
import Goose.Lower.DemandCallMixedBodyLeave

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Lower Goose.Evidence

theorem generated_callee_unit_fallthrough {cfg : Cfg} {ctx : Context} {impl : Impl} {env : Env}
    {initial frame : GIR.Frame} {point : Pt}
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    (post : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩
      (callEntry impl) initial
      (lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)).2
      frame point []) :
    instAt (lowerContextAt cfg.mod ctx impl) point = some (.term (.ret [] none)) := by
  have emptyResults : impl.results = #[] := Array.toList_eq_nil_iff.mp noResults
  let le := lowerEnv cfg.mod impl.vars impl.results.toList
  let body := lowerBlock none (callPre impl) false impl.body le (callEntry impl)
  have bodyPoint : body.2.pp = some point := post.pp
  obtain ⟨block, current, _, _⟩ := LS.pp_some bodyPoint
  have tailRun : emitTerm (.ret [] none) le body.2 = ((), bodyTail impl le body.1 body.2) := by
    unfold bodyTail
    simp [finishFunction, emptyResults, noValue, bind_run, isLive_run current, le]
  have tailExt : ExtT (bodyTail impl le body.1 body.2) (lowerContextAt cfg.mod ctx impl).blocks := by
    rw [lowerContextAt_blocks, lowerImpl_call_blocks]
    exact extT_finish _
  exact (emitTerm_facts tailRun bodyPoint tailExt).2.2.2

theorem accepted_generated_callee_fallthrough_return {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel bodyFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    {caller : Func} {before : LS} {results : List Ty} {initial frame : GIR.Frame} {start point : Pt}
    (wholePost : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
      (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [])
    (read : mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 middle = .ok values middle)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {calleeFrame : GIR.Frame} {entered : St}
    (entry : FunctionEntry (lowerContextAt cfg.mod ctx impl) (frame.depth + 1) values middle calleeFrame entered)
    {taken : Nat} {terminal : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
      ⟨(0, 0), calleeFrame, entered⟩ terminal)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    (calleePost : Post cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (callEntry impl) calleeFrame
      (lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)).2
      terminal.frame terminal.point [])
    (bodyDone : execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .ok (.normal .unit) terminal.state) :
    ∃ afterCall : LS,
      RuntimeStep ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val .unit)) terminal.state ∧
      ExpressionDemandBoundary source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial afterCall
        (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 .unit terminal.state
        (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val .unit)) := by
  have returned := generated_callee_unit_fallthrough noResults noValue calleePost
  exact accepted_generated_unit_call_return source argumentsDone contextAt implAt depth wholePost read extended admitted bounded
    realized entry steps returned bodyDone

#print axioms accepted_generated_callee_fallthrough_return
#print axioms generated_callee_unit_fallthrough
end Goose.Lower
