import Goose.Lower.DemandCallCalleeStopped
import Goose.Lower.DemandCallCoreStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_actual_unit_call_stop {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (fragment : WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    {caller : Func} {before : LS} {results : List Ty} {initial frame : GIR.Frame} {start point : Pt}
    (wholePost : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
      (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [])
    (read : mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 middle = .ok values middle)
    (callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    {taken : Nat} {terminal : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
      ⟨(0, 1 + (callPre impl).length),
        { (callFrame impl middle.nextAct (env.depth + 1) values) with scopes := [(impl.body.scope, middle.nextScope)] },
        { middle with nextAct := middle.nextAct + 1, nextScope := middle.nextScope + 1, store := preStore middle.nextAct middle.nextScope ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) middle.store }⟩ terminal)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ targetFuel terminal stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ sourceFuel, evalExpr sourceFuel cfg env (.call context arguments origin) state = .stop stop after := by
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
  obtain ⟨_, instruction⟩ := Post.def_leaf wholePost definition afterExtended (.val .unit)
  have arity := source.call_arguments_arity contextAt implAt argumentsDone
  have depthAt : frame.depth = env.depth := wholePost.rel.depth
  have below : frame.depth < maxCallDepth := by simpa [depthAt] using depth
  have entry := lowered_function_entry_generated (cfg := cfg) (ctx := ctx) (impl := impl)
    (depth := env.depth + 1) (values := values) (state := middle) arity
  have callerEntry : FunctionEntry (lowerContextAt cfg.mod ctx impl) (frame.depth + 1) values middle
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 } := by
    simpa [depthAt] using entry
  have calleePoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 } :=
    .call callerPoint instruction below read (lower_func_at contextAt implAt) callerEntry
  obtain ⟨bodyFuel, bodyStopped⟩ :=
    accepted_generated_callee_actual_stop source argumentsDone contextAt implAt fragment noResults noValue calleePoint steps stopped nonTimeout
  exact ⟨max argumentFuel bodyFuel + 2,
    accepted_call_source_stop source argumentsDone contextAt implAt depth nonTimeout bodyStopped⟩

#print axioms accepted_generated_actual_unit_call_stop
end Goose.Lower
