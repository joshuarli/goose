import Goose.Lower.DemandCallSliceMixedTerminal
import Goose.Lower.DemandCallSliceActualRun
import Goose.Lower.DemandCallSliceMixedStopped

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence Goose.Proofs.Lower

theorem accepted_generated_slice_mixed_callee_unit_success {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val} (done : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : SliceMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
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
  obtain ⟨taken, remaining, terminal, count, steps, terminalRun, maximal, classification⟩ := runAt_success_maximal_prefix
    (initial := ⟨(0, 0), callFrame impl middle.nextAct (env.depth + 1) values,
      { middle with nextAct := middle.nextAct + 1 }⟩) run
  have terminated : TerminatedBlocks (lowerContextAt cfg.mod ctx impl) := by
    intro block member
    exact Validation.lowerContextAt_terminators cfg.mod ctx impl block (Array.mem_toList_iff.mpr member)
  have entryExt := lowered_callee_entry_extension cfg ctx impl
  obtain ⟨entryBlock, entryAt, _⟩ := entryExt.params (b := 0)
    (blk := ⟨(List.range impl.params.size).zip (callEntryTypes impl), #[]⟩) rfl
  have initial : ∃ instruction, instAt (lowerContextAt cfg.mod ctx impl) (0, 0) = some instruction :=
    terminated_first_instruction terminated entryAt
  obtain ⟨instruction, instructionAt⟩ := steps.has_instruction terminated initial
  obtain ⟨term, rfl⟩ := classification instruction instructionAt
  obtain ⟨residual, bodySteps⟩ := accepted_generated_callee_after_prologue source done contextAt implAt steps maximal
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
    accepted_generated_parameterized_slice_mixed_callee_terminal ready.source rfl (by simpa using fragment) noResults noValue
      (.context contextAt implAt) ready.owned ready.occurrence ready.rows coverage admitted bounded ready.cells realized ready.input entry
      (by simpa [frameScopes] using bodySteps) instructionAt maximal
  have returned := generated_callee_unit_fallthrough noResults noValue post
  cases remaining with
  | zero =>
    change timeout terminal.state = .ok value after at terminalRun
    simp [timeout, M.stop] at terminalRun
  | succ remaining =>
    have finalRun : runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ terminal.point terminal.frame
        (remaining + 1) terminal.state = .ok .unit terminal.state := by
      rw [runAt_ret0 returned remaining]
      rfl
    obtain ⟨valueEq, stateEq⟩ := Res.ok.inj (terminalRun.symm.trans finalRun)
    subst value
    subst after
    exact ⟨rfl, bodyFuel, bodyDone⟩



#print axioms accepted_generated_slice_mixed_callee_unit_success
theorem accepted_generated_slice_mixed_callee_unit_stopped_run {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val} (done : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : SliceMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
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
  obtain ⟨taken, remaining, terminal, count, steps, terminalRun, maximal, classification⟩ := runAt_nonTimeout_stopped_prefix nonTimeout
    (initial := ⟨(0, 0), callFrame impl middle.nextAct (env.depth + 1) values,
      { middle with nextAct := middle.nextAct + 1 }⟩) run
  have terminated : TerminatedBlocks (lowerContextAt cfg.mod ctx impl) := by
    intro block member
    exact Validation.lowerContextAt_terminators cfg.mod ctx impl block (Array.mem_toList_iff.mpr member)
  have entryExt := lowered_callee_entry_extension cfg ctx impl
  obtain ⟨entryBlock, entryAt, _⟩ := entryExt.params (b := 0)
    (blk := ⟨(List.range impl.params.size).zip (callEntryTypes impl), #[]⟩) rfl
  have initial : ∃ instruction, instAt (lowerContextAt cfg.mod ctx impl) (0, 0) = some instruction :=
    terminated_first_instruction terminated entryAt
  obtain ⟨instruction, instructionAt⟩ := steps.has_instruction terminated initial
  obtain ⟨residual, bodySteps⟩ := accepted_generated_callee_after_prologue source done contextAt implAt steps maximal
  rcases classification with stopped | ⟨term, terminalAt⟩ | missing
  · exact accepted_generated_slice_mixed_callee_actual_stop source done contextAt implAt fragment noResults noValue entry bodySteps stopped nonTimeout
  · have coverage : (⟨[], []⟩ : RetainedSsaMap).Covers ⟨[], []⟩ := by simp [RetainedSsaMap.Covers]
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
      accepted_generated_parameterized_slice_mixed_callee_terminal ready.source rfl (by simpa using fragment) noResults noValue
        (.context contextAt implAt) ready.owned ready.occurrence ready.rows coverage admitted bounded ready.cells realized ready.input entry
        (by simpa [frameScopes] using bodySteps) terminalAt maximal
    have returned := generated_callee_unit_fallthrough noResults noValue post
    cases remaining with
    | zero =>
      change timeout terminal.state = .stop stop after at terminalRun
      simp [timeout, M.stop] at terminalRun
      exact (nonTimeout terminalRun.1.symm).elim
    | succ remaining =>
      have normal : runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ terminal.point terminal.frame
          (remaining + 1) terminal.state = .ok .unit terminal.state := by
        rw [runAt_ret0 returned remaining]
        rfl
      cases normal.symm.trans terminalRun
  · rw [missing] at instructionAt
    cases instructionAt



#print axioms accepted_generated_slice_mixed_callee_unit_stopped_run
end Goose.Lower
