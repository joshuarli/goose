import Goose.Lower.DemandCallBoolCallee

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_actual_bool_call {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val}
    (argumentsDone : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[context]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (depth : env.depth < maxCallDepth)
    (fragment : WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {boolean : Bool} (hasValue : impl.body.value = some (.bool boolean))
    {caller : Func} {before : LS} {results : List Ty} {initial frame : GIR.Frame} {start point : Pt}
    (wholePost : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial
      (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).2 frame point [])
    (read : mapList (getVal frame) (lowerArgs arguments (lowerEnv cfg.mod env.vars results) before).1 middle = .ok values middle)
    (callerPoint : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {taken : Nat} {terminal : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
      ⟨(0, 1 + (callPre impl).length),
        { (callFrame impl middle.nextAct (env.depth + 1) values) with scopes := [(impl.body.scope, middle.nextScope)] },
        { middle with nextAct := middle.nextAct + 1, nextScope := middle.nextScope + 1, store := preStore middle.nextAct middle.nextScope ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) middle.store }⟩ terminal)
    (returned : instAt (lowerContextAt cfg.mod ctx impl) terminal.point = some (.term (.ret [(lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)).1] none))) :
    ∃ afterCall : LS,
      RuntimeStep ⟨cfg.profile, lower cfg.mod⟩ caller point frame middle (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val (.bool boolean))) terminal.state ∧
      ExpressionDemandBoundary source map ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ before initial afterCall
        (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.bool boolean) terminal.state
        (point.1, point.2 + 1)
        (frame.set (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).1 (.val (.bool boolean))) := by
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
  obtain ⟨_, instruction⟩ := Post.def_leaf wholePost definition afterExtended (.val (.bool boolean))
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
  obtain ⟨bodyFuel, bodyDone, ⟨total, calleeTrace⟩, calleePost⟩ :=
    accepted_generated_callee_actual_bool_return source argumentsDone contextAt implAt fragment hasValue calleePoint steps returned
  exact accepted_generated_callee_value_fallthrough_return source argumentsDone contextAt implAt depth wholePost read extended admitted bounded
    realized callerEntry calleeTrace hasValue calleePost bodyDone

#print axioms accepted_generated_actual_bool_call
end Goose.Lower
