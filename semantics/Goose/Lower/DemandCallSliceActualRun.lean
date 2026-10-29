import Goose.Lower.DemandCallSliceTerminal
import Goose.Lower.DemandCallSliceBodyStopped
import Goose.Lower.DemandCallActualCalleeRun

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence Goose.Proofs.Lower

theorem accepted_generated_slice_callee_unit_success {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val} (done : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : SliceAssignmentStatements impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 })
    {targetFuel : Nat} {value : Val} {after : St}
    (run : runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) targetFuel { middle with nextAct := middle.nextAct + 1 } = .ok value after) :
    value = .unit ∧ ∃ bodyFuel, execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .ok (.normal .unit) after := by
  obtain ⟨ready⟩ := accepted_generated_callee_ready source done contextAt implAt
  apply accepted_generated_callee_unit_success_of_terminal source done contextAt implAt ?_ noResults noValue entry run
  intro taken terminal term terminalFuel bodySteps instructionAt maximal
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
  obtain ⟨bodyFuel, bodyDone, _, _, post, _⟩ :=
    accepted_generated_parameterized_slice_callee_terminal ready.source rfl (by simpa using fragment) noResults noValue
      (.context contextAt implAt) ready.owned ready.occurrence ready.rows coverage admitted bounded ready.cells realized ready.input entry
      (by simpa [frameScopes] using bodySteps) instructionAt maximal
  exact ⟨bodyFuel, bodyDone, post⟩

#print axioms accepted_generated_slice_callee_unit_success
theorem accepted_generated_slice_callee_unit_stopped_run {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val} (done : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : SliceAssignmentStatements impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 })
    {targetFuel : Nat} {stop : Stop} {after : St}
    (run : runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) targetFuel { middle with nextAct := middle.nextAct + 1 } = .stop stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ bodyFuel, execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .stop stop after := by
  obtain ⟨ready⟩ := accepted_generated_callee_ready source done contextAt implAt
  apply accepted_generated_callee_unit_stopped_of_endpoints source done contextAt implAt ?_ ?_ noResults noValue entry run nonTimeout
  · intro taken terminal terminalFuel stop after bodySteps stopped nonTimeout
    exact accepted_generated_slice_callee_actual_stop source done contextAt implAt fragment noResults noValue entry bodySteps stopped nonTimeout
  · intro taken terminal term terminalFuel bodySteps terminalAt maximal
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
    obtain ⟨bodyFuel, bodyDone, _, _, post, _⟩ :=
      accepted_generated_parameterized_slice_callee_terminal ready.source rfl (by simpa using fragment) noResults noValue
        (.context contextAt implAt) ready.owned ready.occurrence ready.rows coverage admitted bounded ready.cells realized ready.input entry
        (by simpa [frameScopes] using bodySteps) terminalAt maximal
    exact ⟨bodyFuel, bodyDone, post⟩

#print axioms accepted_generated_slice_callee_unit_stopped_run
end Goose.Lower
