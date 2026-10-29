import Goose.Lower.DemandCallSliceTerminal
import Goose.Lower.DemandCallBodyStopped
import Goose.Lower.DemandCallCalleeReady

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_parameterized_slice_callee_stopped {cfg : Cfg} {ctx : Context} {impl : Impl} {env : Env}
    {pre : List (VarId × Val)} {state : St} (source : BlockSource cfg env pre impl.body state)
    (envVars : env.vars = impl.vars)
    (fragment : SliceAssignmentStatements impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod (lowerContextAt cfg.mod ctx impl)
      (lowerEnv cfg.mod env.vars impl.results.toList) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod (lowerContextAt cfg.mod ctx impl)
      (lowerEnv cfg.mod env.vars impl.results.toList) root source.path (.block none (callPre impl) false impl.body) (callEntry impl))
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded (callEntry impl).vals.size) {initial : GIR.Frame}
    (cells : PreRel initial (callPre impl) pre)
    (realized : map.Realizes cfg.mod source.world env ⟨(0, 0), initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩
      impl.results.toList none source.typingEnv source.rootsEnv (callEntry impl) initial (0, 0))
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0) initial state)
    {taken : Nat} {terminal : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
      ⟨(0, 1 + (callPre impl).length), { initial with scopes := (impl.body.scope, state.nextScope) :: initial.scopes },
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }⟩ terminal)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ targetFuel terminal stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ sourceFuel, execBlock sourceFuel cfg env pre impl.body state = .stop stop after := by
  let cx : FnCtx := ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩
  have extended : ExtT (lowerBlock none (callPre impl) false impl.body
      (lowerEnv cfg.mod env.vars impl.results.toList) (callEntry impl)).2 cx.fn.blocks := by
    let le := lowerEnv cfg.mod impl.vars impl.results.toList
    let body := lowerBlock none (callPre impl) false impl.body le (callEntry impl)
    have tailExtension : ExtT (Goose.Proofs.Lower.bodyTail impl le body.1 body.2) (lowerContextAt cfg.mod ctx impl).blocks := by
      rw [lowerContextAt_blocks, lowerImpl_call_blocks]
      exact Goose.Proofs.Lower.extT_finish _
    have bodyExtension := tailExtension.of_adv
      (advB_finishFunction impl body.1 le body.2 (finishFunction impl body.1 le body.2).1
        (Goose.Proofs.Lower.bodyTail impl le body.1 body.2) rfl)
    simpa only [envVars] using bodyExtension
  obtain ⟨body, bodyOffset, bodyCanonical, bodyOccurrence, bodyRows, bodyOwned, bodyAdmitted, bodyEntryBounded, bodyEntryRealized, bodyInput, bodyProloguePost, progress, bodyReached⟩ :=
    accepted_generated_parameterized_slice_body_stopped_canonical source fragment selected owned occurrence rows coverage admitted bounded cells realized input extended entry
      (by simpa using steps) stopped nonTimeout
  cases progress with
  | aborted sourceFuel evaluated =>
    have raw : execStmts sourceFuel cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes }
        impl.body.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } =
        .stop stop after := by
      simp only [prepareLoopFlow_none, bind_apply] at evaluated
      cases run : execStmts sourceFuel cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes }
          impl.body.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } with
      | stop reason final => simpa [run] using evaluated
      | ok flow final =>
        have normal := fragment.normal run
        subst flow
        simp [run, prepareReturn, pure_apply] at evaluated
    refine ⟨sourceFuel + 1, ?_⟩
    cases bodyEq : impl.body with
    | mk scope statements value =>
      simp only [bodyEq, Core.Block.scope, Core.Block.stmts] at raw
      simp [bodyEq, execBlock, bind_apply, freshScope, bindAll_eq, raw]
  | @complete sourceFuel consumed remaining boundary flow count executed residual evaluated ending =>
    have statements : execStmts sourceFuel cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes }
        impl.body.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } =
        .ok (.normal .unit) boundary.state := by
      simp only [prepareLoopFlow_none, bind_apply] at evaluated
      cases raw : execStmts sourceFuel cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes }
          impl.body.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } with
      | stop stop after => simp [raw] at evaluated
      | ok rawFlow after =>
        have normal := fragment.normal raw
        subst rawFlow
        simp only [raw, prepareReturn, pure_apply, Res.ok.injEq] at evaluated
        obtain ⟨_, rfl⟩ := evaluated
        rfl
    have normal : flow = .normal .unit := by
      simp only [prepareLoopFlow_none, bind_apply, statements, prepareReturn, pure_apply, Res.ok.injEq] at evaluated
      exact evaluated.1.symm
    subst flow
    cases ending with
    | transfer abnormal _ => exact (abnormal .unit rfl).elim
    | normal sequencePost result bodyBounded bodyRealized =>
      have nextPost : Post cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } cx
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars impl.results.toList) (callEntry impl) (callPre impl) impl.body)
          { initial with scopes := (impl.body.scope, state.nextScope) :: initial.scopes }
          (lowerStmts none impl.body.stmts (lowerEnv cfg.mod env.vars impl.results.toList)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars impl.results.toList) (callEntry impl) (callPre impl) impl.body)).2
          boundary.frame boundary.point [] := by
        simpa [bodyOffset, lowerStmts, pure_run] using sequencePost
      rcases residual.uncons with ⟨_, same⟩ | ⟨rest, afterLeave, length, leaveStep, tail⟩
      · subst terminal
        have site := GeneratedDemandInstruction.blockLeave_auto occurrence rows (by simpa [noValue, lowerBlockValue, demandBlockValueBefore, pure_run] using nextPost.pp) extended
        have expected : DemandInstructionStep cx targetFuel boundary
            ⟨(boundary.point.1, boundary.point.2 + 1), { boundary.frame with scopes := env.scopes },
              { boundary.state with store := releaseVars env.vars env.act impl.body.scope state.nextScope env.vars.size boundary.state.store }⟩ :=
          .effect site.instruction (block_leave_exec nextPost.rel boundary.state)
        exact (stopped.excludes_step_nonTimeout nonTimeout expected).elim
      · obtain ⟨bodyDone, finalPost, bodyResult, finalBounded, finalRealized⟩ :=
          accepted_generated_parameterized_body_leave source selected owned occurrence rows coverage admitted bounded cells realized input extended entry noValue statements nextPost leaveStep
        have fallthrough := generated_callee_unit_fallthrough noResults noValue (by simpa [envVars] using finalPost)
        rcases tail.uncons with ⟨_, same⟩ | ⟨_, _, _, nextStep, _⟩
        · subst terminal
          cases stopped with
          | timeout => exact (nonTimeout rfl).elim
          | definition found execution => cases fallthrough.symm.trans found
          | effect found execution => cases fallthrough.symm.trans found
        · exact (runtimeStep_excludes_return fallthrough nextStep).elim


#print axioms accepted_generated_parameterized_slice_callee_stopped
theorem accepted_generated_slice_callee_actual_stop {cfg : Cfg} {env : Env} {state middle : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {fuel : Nat} {values : List Val} (done : mapList (evalArg fuel cfg env) arguments state = .ok values middle)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : SliceAssignmentStatements impl.body.stmts)
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
  exact accepted_generated_parameterized_slice_callee_stopped ready.source rfl (by simpa using fragment) noResults noValue
    (.context contextAt implAt) ready.owned ready.occurrence ready.rows coverage admitted bounded ready.cells realized ready.input entry
    (by simpa [frameScopes] using steps) stopped nonTimeout


#print axioms accepted_generated_slice_callee_actual_stop
end Goose.Lower
