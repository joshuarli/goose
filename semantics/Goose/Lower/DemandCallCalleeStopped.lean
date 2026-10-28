import Goose.Lower.DemandCallCalleeReady
import Goose.Lower.DemandCallBodyStopped

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_callee_actual_stop {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {fuel : Nat} {values : List Val} (done : mapList (evalArg fuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 })
    {taken : Nat} {terminal : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
      ⟨(0, 1 + (callPre impl).length),
        { (callFrame impl middle.nextAct (env.depth + 1) values) with scopes := [(impl.body.scope, middle.nextScope)] },
        { middle with nextAct := middle.nextAct + 1, nextScope := middle.nextScope + 1, store := preStore middle.nextAct middle.nextScope ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) middle.store }⟩ terminal)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ targetFuel terminal stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ bodyFuel, execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .stop stop after := by
  obtain ⟨ready⟩ := accepted_generated_callee_ready source done contextAt implAt
  have coverage : (⟨[], []⟩ : RetainedSsaMap).Covers ⟨[], []⟩ := by simp [RetainedSsaMap.Covers]
  have admitted : (⟨[], []⟩ : RetainedSsaMap).Admitted cfg.mod.profile ready.source.context.retained := by simp [RetainedSsaMap.Admitted]
  have bounded : (⟨[], []⟩ : RetainedSsaMap).Bounded (callEntry impl).vals.size := by simp [RetainedSsaMap.Bounded]
  have realized : (⟨[], []⟩ : RetainedSsaMap).Realizes cfg.mod ready.source.world
      ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ⟨(0, 0), callFrame impl middle.nextAct (env.depth + 1) values, { middle with nextAct := middle.nextAct + 1 }⟩ := by
    simp [RetainedSsaMap.Realizes, RetainedOperandsAt]
  obtain ⟨_, scopes, _⟩ := bindCallParams_frame ⟨middle.nextAct, [], {}, env.depth + 1⟩
    ((List.range impl.params.size).zip (callEntryTypes impl)) (values.map RVal.val)
  have frameScopes : (callFrame impl middle.nextAct (env.depth + 1) values).scopes = [] := by
    simpa only [callFrame] using scopes
  exact accepted_generated_parameterized_callee_stopped ready.source rfl (by simpa using fragment) noResults noValue
    (.context contextAt implAt) ready.owned ready.occurrence ready.rows coverage admitted bounded ready.cells realized ready.input entry
    (by simpa [frameScopes] using steps) stopped nonTimeout

#print axioms accepted_generated_callee_actual_stop
end Goose.Lower
