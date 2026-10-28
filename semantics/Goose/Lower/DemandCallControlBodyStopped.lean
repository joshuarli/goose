import Goose.Lower.DemandCallBodyStopped
import Goose.Lower.DemandCallControlBodyReturn

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_parameterized_callee_control_stopped {cfg : Cfg} {ctx : Context} {impl : Impl} {env : Env}
    {pre : List (VarId × Val)} {state : St} (source : BlockSource cfg env pre impl.body state)
    (envVars : env.vars = impl.vars)
    (fragment : WhileMixedStatements cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } impl.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : impl.body.value = some expression)
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
    accepted_generated_parameterized_mixed_body_stopped_canonical source fragment selected owned occurrence rows coverage admitted bounded cells realized input extended entry
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
      let le := lowerEnv cfg.mod env.vars impl.results.toList
      let valueStart := demandBlockValueBefore le (callEntry impl) none (callPre impl) impl.body
      have wholeStatements : Post cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } cx
          (callEntry impl) initial valueStart boundary.frame boundary.point [] := by
        simpa [valueStart, demandBlockValueBefore] using bodyProloguePost.comp nextPost
      obtain ⟨child, childAt, childOccurrence, childRows, valueProgress⟩ :=
        accepted_generated_parameterized_value_stopped source body bodyCanonical hasValue form selected owned bodyOccurrence bodyRows
          coverage bodyAdmitted bodyEntryBounded bodyEntryRealized bodyInput statements nextPost extended residual stopped nonTimeout
      cases valueProgress with
      | aborted valueFuel valueStopped =>
        let common : Nat := max sourceFuel valueFuel
        have statementsRaised := ((Goose.Proofs.Fuel.monoAll sourceFuel common (by dsimp [common]; omega)).stmts cfg
          { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } impl.body.stmts
          { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }).1 _ _ statements
        have stoppedRaised : evalExpr common cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes }
            expression boundary.state = .stop stop after := by
          rcases ((Goose.Proofs.Fuel.monoAll valueFuel common (by dsimp [common]; omega)).expr cfg
            { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } expression boundary.state).2 _ _ valueStopped with timeout | done
          · have notTimeout : Goose.Proofs.Fuel.isTimeout stop = false := by
              cases stop with
              | timeout => exact (nonTimeout rfl).elim
              | abort | exit | fault => rfl
            rw [notTimeout] at timeout
            cases timeout
          · exact done
        refine ⟨common + 1, ?_⟩
        cases bodyEq : impl.body with
        | mk scope stmts value =>
          simp only [bodyEq, Core.Block.scope, Core.Block.stmts, Core.Block.value] at hasValue statementsRaised stoppedRaised ⊢
          subst value
          simp [execBlock, freshScope, bindAll_eq, bind_apply, statementsRaised, stoppedRaised]
      | @complete valueFuel valueConsumed valueRemaining valuePoint value count valueSteps afterValue valueEvaluated valueBoundary =>
        let common : Nat := max sourceFuel valueFuel
        have statementsRaised := ((Goose.Proofs.Fuel.monoAll sourceFuel common (by dsimp [common]; omega)).stmts cfg
          { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } impl.body.stmts
          { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }).1 _ _ statements
        have valueRaised := ((Goose.Proofs.Fuel.monoAll valueFuel common (by dsimp [common]; omega)).expr cfg
          { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } expression boundary.state).1 _ _ valueEvaluated
        have valueDone : valueFlow common cfg impl.body.value
            { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } (.normal .unit) boundary.state =
            .ok (.normal value) valuePoint.state := by
          rw [hasValue]
          simp [valueFlow, bind_apply, valueRaised, pure_apply]
        have wholeValue : Post cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } cx
            (callEntry impl) initial (lowerBlockValue false impl.body.value le valueStart).2 valuePoint.frame valuePoint.point
            [((lowerBlockValue false impl.body.value le valueStart).1, .val value)] := by
          simpa [hasValue, lowerBlockValue] using wholeStatements.comp valueBoundary.post
        rcases afterValue.uncons with ⟨_, same⟩ | ⟨remaining, afterLeave, laterLength, leaveStep, tail⟩
        · subst terminal
          have site := GeneratedDemandInstruction.blockLeave_auto occurrence rows wholeValue.pp extended
          have expected : DemandInstructionStep cx targetFuel valuePoint
              ⟨(valuePoint.point.1, valuePoint.point.2 + 1), { valuePoint.frame with scopes := env.scopes },
                { valuePoint.state with store := releaseVars env.vars env.act impl.body.scope state.nextScope env.vars.size valuePoint.state.store }⟩ :=
            .effect site.instruction (block_leave_exec wholeValue.rel valuePoint.state)
          exact (stopped.excludes_step_nonTimeout nonTimeout expected).elim
        · obtain ⟨_, _, _, _, bodyDone, finalPost, bodyResult, finalBounded, finalDemand⟩ :=
            accepted_generated_block_leave_runtime_step source occurrence rows coverage admitted bounded realized
              statementsRaised valueDone wholeValue extended leaveStep
          have bodyValueId := generated_block_value_result le (callEntry impl) none (callPre impl) false impl.body
          have finalCells : Post cfg env cx (callEntry impl) initial
              (lowerBlock none (callPre impl) false impl.body le (callEntry impl)).2 afterLeave.frame afterLeave.point
              [((lowerBlock none (callPre impl) false impl.body le (callEntry impl)).1, .val value)] := by
            rw [bodyValueId]
            exact finalPost
          have calleePost : Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩
              (callEntry impl) initial
              (lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)).2
              afterLeave.frame afterLeave.point [((lowerBlock none (callPre impl) false impl.body
                (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)).1, .val value)] := by
            simpa [le, cx, envVars] using finalCells
          have fallthrough := generated_callee_value_fallthrough hasValue calleePost
          rcases tail.uncons with ⟨_, rfl⟩ | ⟨_, _, _, nextStep, _⟩
          · cases stopped with
            | timeout => exact (nonTimeout rfl).elim
            | definition found execution => cases fallthrough.1.symm.trans found
            | effect found execution => cases fallthrough.1.symm.trans found
          · exact (runtimeStep_excludes_return fallthrough.1 nextStep).elim

#print axioms accepted_generated_parameterized_callee_control_stopped
end Goose.Lower
