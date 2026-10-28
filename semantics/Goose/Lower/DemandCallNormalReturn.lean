import Goose.Lower.DemandCallCoreReturn
import Goose.Lower.DemandCallActualReturn

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_unit_call_return {cfg : Cfg} {env : Env} {state middle : St}
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
    (returned : instAt (lowerContextAt cfg.mod ctx impl) terminal.point = some (.term (.ret [] none)))
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
  let le := lowerEnv cfg.mod env.vars results
  obtain ⟨ids, middleBuilder, afterCall, argsRun, definition, tail⟩ := lowerExpr_call_split
    (show lowerExpr (.call context arguments origin) le before =
      ((lowerExpr (.call context arguments origin) le before).1, (lowerExpr (.call context arguments origin) le before).2) from rfl)
  have afterExtended : ExtT afterCall caller.blocks := by
    rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
    · exact extended.of_adv (adv_emitTerm term)
    · exact extended
  have idsEq : ids = (lowerArgs arguments le before).1 := by rw [argsRun]
  have middleEq : middleBuilder = (lowerArgs arguments le before).2 := by rw [argsRun]
  subst ids
  subst middleBuilder
  obtain ⟨post, instruction⟩ := Post.def_leaf wholePost definition afterExtended (.val .unit)
  have below : frame.depth < maxCallDepth := by simpa [wholePost.rel.depth] using depth
  have lookup := lower_func_at contextAt implAt
  have returnStep := actual_call_unit_return_runtime_step instruction below read lookup entry steps returned
  have boundary := accepted_call_normal_demand_return source argumentsDone contextAt implAt depth bodyDone admitted bounded realized post
  exact ⟨afterCall, returnStep, boundary⟩

#print axioms accepted_generated_unit_call_return
end Goose.Lower
