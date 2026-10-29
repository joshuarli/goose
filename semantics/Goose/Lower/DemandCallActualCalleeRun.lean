import Goose.Lower.DemandCallBoolCallee
import Goose.Lower.DemandCallCalleeStopped
import Goose.Lower.DemandCallBoolCalleeStopped
import Goose.Lower.DemandRunAtSuccess
import Goose.Lower.DemandRuntimeInstruction
import Goose.Lower.Validation.CfgFunctionCompletion

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence Goose.Proofs.Lower

theorem accepted_generated_callee_after_prologue {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {fuel : Nat} {values : List Val} (done : mapList (evalArg fuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    {taken targetFuel : Nat} {terminal : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
      ⟨(0, 0), callFrame impl middle.nextAct (env.depth + 1) values, { middle with nextAct := middle.nextAct + 1 }⟩ terminal)
    (maximal : ∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ targetFuel terminal next) :
    ∃ remaining, DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ remaining
      ⟨(0, 1 + (callPre impl).length),
        { (callFrame impl middle.nextAct (env.depth + 1) values) with scopes := [(impl.body.scope, middle.nextScope)] },
        { middle with nextAct := middle.nextAct + 1, nextScope := middle.nextScope + 1, store := preStore middle.nextAct middle.nextScope ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) middle.store }⟩ terminal := by
  obtain ⟨ready⟩ := accepted_generated_callee_ready source done contextAt implAt
  let le := lowerEnv cfg.mod impl.vars impl.results.toList
  let body := lowerBlock none (callPre impl) false impl.body le (callEntry impl)
  have tailExtension : ExtT (bodyTail impl le body.1 body.2) (lowerContextAt cfg.mod ctx impl).blocks := by
    rw [lowerContextAt_blocks, lowerImpl_call_blocks]
    exact extT_finish _
  have bodyExtension := tailExtension.of_adv
    (advB_finishFunction impl body.1 le body.2 (finishFunction impl body.1 le body.2).1
      (bodyTail impl le body.1 body.2) rfl)
  let pre := (impl.params.toList.zip values).map fun item => (item.1.var, item.2)
  have lowered : lowerBlock none (callPre impl) false impl.body le (callEntry impl) = (body.1, body.2) := rfl
  have effects := accepted_block_parameter_prologue_effects ready.source lowered ready.input.atPoint bodyExtension
    ready.input.related ready.cells pre.length (by dsimp [pre]; exact Nat.le_refl _)
  obtain ⟨_, scopes, _⟩ := bindCallParams_frame ⟨middle.nextAct, [], {}, env.depth + 1⟩
    ((List.range impl.params.size).zip (callEntryTypes impl)) (values.map RVal.val)
  have frameScopes : (callFrame impl middle.nextAct (env.depth + 1) values).scopes = [] := by
    simpa only [callFrame] using scopes
  obtain ⟨remaining, count, residual⟩ := effects.compare_maximal steps maximal
  refine ⟨remaining, ?_⟩
  have equalLength : (callPre impl).length = pre.length := ready.cells.length
  have takeAll : ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)).take pre.length =
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) := by
    dsimp [pre]
    exact List.take_length
  simpa only [equalLength, takeAll, frameScopes, Nat.zero_add, List.nil_append] using residual

theorem accepted_generated_callee_unit_success_of_terminal {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val} (done : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (reflect : ∀ {taken : Nat} {terminal : DemandRuntimePoint} {term : Term} {terminalFuel : Nat},
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
        ⟨(0, 1 + (callPre impl).length),
          { (callFrame impl middle.nextAct (env.depth + 1) values) with scopes := [(impl.body.scope, middle.nextScope)] },
          { middle with nextAct := middle.nextAct + 1, nextScope := middle.nextScope + 1, store := preStore middle.nextAct middle.nextScope ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) middle.store }⟩ terminal →
      instAt (lowerContextAt cfg.mod ctx impl) terminal.point = some (.term term) →
      (∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ terminalFuel terminal next) →
      ∃ bodyFuel, execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
        ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
        { middle with nextAct := middle.nextAct + 1 } = .ok (.normal .unit) terminal.state ∧
      Post cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩ ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩
        (callEntry impl) (callFrame impl middle.nextAct (env.depth + 1) values)
        (lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)).2
        terminal.frame terminal.point [])
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 })
    {targetFuel : Nat} {value : Val} {after : St}
    (run : runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) targetFuel { middle with nextAct := middle.nextAct + 1 } = .ok value after) :
    value = .unit ∧ ∃ bodyFuel, execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .ok (.normal .unit) after := by
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
  obtain ⟨bodyFuel, bodyDone, post⟩ := reflect bodySteps instructionAt maximal
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


theorem accepted_generated_callee_unit_success {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val} (done : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : WhileMixedStatements cfg
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
    accepted_generated_parameterized_callee_terminal ready.source rfl (by simpa using fragment) noResults noValue
      (.context contextAt implAt) ready.owned ready.occurrence ready.rows coverage admitted bounded ready.cells realized ready.input entry
      (by simpa [frameScopes] using bodySteps) instructionAt maximal
  exact ⟨bodyFuel, bodyDone, post⟩

#print axioms accepted_generated_callee_unit_success_of_terminal

theorem accepted_generated_callee_literal_success {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val} (done : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {expression : Expr} {literalValue : Val} {operation : Op}
    (literal : CallScalarLiteral expression literalValue operation) (hasValue : impl.body.value = some expression)
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 })
    {targetFuel : Nat} {value : Val} {after : St}
    (run : runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) targetFuel { middle with nextAct := middle.nextAct + 1 } = .ok value after) :
    value = literalValue ∧ ∃ bodyFuel, execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .ok (.normal (literalValue)) after := by
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
    accepted_generated_parameterized_callee_literal_terminal ready.source rfl (by simpa using fragment) literal hasValue
      (.context contextAt implAt) ready.owned ready.occurrence ready.rows coverage admitted bounded ready.cells realized ready.input entry
      (by simpa [frameScopes] using bodySteps) instructionAt maximal
  obtain ⟨returned, returnCell⟩ := generated_callee_value_fallthrough hasValue post
  cases remaining with
  | zero =>
    change timeout terminal.state = .ok value after at terminalRun
    simp [timeout, M.stop] at terminalRun
  | succ remaining =>
    have finalRun : runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ terminal.point terminal.frame
        (remaining + 1) terminal.state = .ok (literalValue) terminal.state := by
      rw [runAt_ret1 returned returnCell remaining]
      rfl
    obtain ⟨valueEq, stateEq⟩ := Res.ok.inj (terminalRun.symm.trans finalRun)
    subst value
    subst after
    exact ⟨rfl, bodyFuel, bodyDone⟩


theorem accepted_generated_callee_bool_success {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val} (done : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {boolean : Bool} (hasValue : impl.body.value = some (.bool boolean))
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 })
    {targetFuel : Nat} {value : Val} {after : St}
    (run : runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) targetFuel { middle with nextAct := middle.nextAct + 1 } = .ok value after) :
    value = .bool boolean ∧ ∃ bodyFuel, execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .ok (.normal (.bool boolean)) after := by
  exact accepted_generated_callee_literal_success source done contextAt implAt fragment (.boolean boolean) hasValue entry run

theorem accepted_generated_callee_unit_stopped_run {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val} (done : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : WhileMixedStatements cfg
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
  · exact accepted_generated_callee_actual_stop source done contextAt implAt fragment noResults noValue entry bodySteps stopped nonTimeout
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
      accepted_generated_parameterized_callee_terminal ready.source rfl (by simpa using fragment) noResults noValue
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

theorem accepted_generated_callee_literal_stopped_run {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val} (done : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {expression : Expr} {literalValue : Val} {operation : Op}
    (literal : CallScalarLiteral expression literalValue operation) (hasValue : impl.body.value = some expression)
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
  · exact accepted_generated_callee_actual_literal_stop source done contextAt implAt fragment literal hasValue entry bodySteps stopped nonTimeout
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
      accepted_generated_parameterized_callee_literal_terminal ready.source rfl (by simpa using fragment) literal hasValue
        (.context contextAt implAt) ready.owned ready.occurrence ready.rows coverage admitted bounded ready.cells realized ready.input entry
        (by simpa [frameScopes] using bodySteps) terminalAt maximal
    obtain ⟨returned, returnCell⟩ := generated_callee_value_fallthrough hasValue post
    cases remaining with
    | zero =>
      change timeout terminal.state = .stop stop after at terminalRun
      simp [timeout, M.stop] at terminalRun
      exact (nonTimeout terminalRun.1.symm).elim
    | succ remaining =>
      have normal : runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ terminal.point terminal.frame
          (remaining + 1) terminal.state = .ok (literalValue) terminal.state := by
        rw [runAt_ret1 returned returnCell remaining]
        rfl
      cases normal.symm.trans terminalRun
  · rw [missing] at instructionAt
    cases instructionAt


theorem accepted_generated_callee_bool_stopped_run {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {argumentFuel : Nat} {values : List Val} (done : mapList (evalArg argumentFuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {boolean : Bool} (hasValue : impl.body.value = some (.bool boolean))
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) { middle with nextAct := middle.nextAct + 1 })
    {targetFuel : Nat} {stop : Stop} {after : St}
    (run : runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
      (callFrame impl middle.nextAct (env.depth + 1) values) targetFuel { middle with nextAct := middle.nextAct + 1 } = .stop stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ bodyFuel, execBlock bodyFuel cfg ⟨impl.vars, middle.nextAct, [], env.depth + 1⟩
      ((impl.params.toList.zip values).map fun item => (item.1.var, item.2)) impl.body
      { middle with nextAct := middle.nextAct + 1 } = .stop stop after := by
  exact accepted_generated_callee_literal_stopped_run source done contextAt implAt fragment (.boolean boolean) hasValue entry run nonTimeout

#print axioms accepted_generated_callee_bool_stopped_run

#print axioms accepted_generated_callee_unit_stopped_run
#print axioms accepted_generated_callee_bool_success

#print axioms accepted_generated_callee_unit_success
#print axioms accepted_generated_callee_after_prologue
end Goose.Lower
