import Goose.Lower.DemandCallBoolBodyReturn
import Goose.Lower.DemandParameterizedValueProgress

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_parameterized_callee_control_terminal {cfg : Cfg} {ctx : Context} {impl : Impl} {env : Env}
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
    {term : Term} (terminalAt : instAt (lowerContextAt cfg.mod ctx impl) terminal.point = some (.term term))
    {targetFuel : Nat} (maximal : ∀ next, ¬ DemandInstructionStep
      ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ targetFuel terminal next) :
    ∃ (value : Val) (fuel : Nat), execBlock fuel cfg env pre impl.body state = .ok (.normal value) terminal.state ∧
      BlockResult source (.normal value) terminal.state ∧
      (∃ total, DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ total
        ⟨(0, 0), initial, state⟩ terminal) ∧
      Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩
        (callEntry impl) initial
        (lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)).2
        terminal.frame terminal.point [((lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)).1, .val value)] ∧ map.Realizes cfg.mod source.world env terminal := by
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
  have prologue := accepted_block_parameter_prologue_trace source
    (show lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod env.vars impl.results.toList) (callEntry impl) =
      ((lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod env.vars impl.results.toList) (callEntry impl)).1,
        (lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod env.vars impl.results.toList) (callEntry impl)).2) from rfl)
    input.atPoint extended input.related cells pre.length (by omega)
  have wholeTrace : DemandRuntimePrefix cx (pre.length + 1 + taken) ⟨(0, 0), initial, state⟩ terminal := by
    apply prologue.append
    simpa [cells.length] using steps
  obtain ⟨body, bodyOffset, bodyCanonical, bodyOccurrence, bodyRows, bodyOwned, bodyAdmitted, bodyEntryBounded, bodyEntryRealized, bodyInput, bodyProloguePost, decomposition, bodyReached⟩ :=
    accepted_generated_parameterized_mixed_body_canonical source fragment selected owned occurrence rows coverage admitted bounded cells realized input extended entry
      (by simpa using steps)
  cases decomposition.progress with
  | interior cursor => exact (cursor.whileMixed_excludes_maximal_terminal terminalAt maximal).elim
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
        accepted_generated_parameterized_value_progress source body bodyCanonical hasValue form selected owned bodyOccurrence bodyRows
          coverage bodyAdmitted bodyEntryBounded bodyEntryRealized bodyInput statements nextPost extended residual
      cases valueProgress.progress with
      | interior cursor =>
        rcases cursor.progress with ⟨id, operation, instruction⟩ | ⟨next, progress⟩
        · cases instruction.symm.trans terminalAt
        · exact (maximal next (progress targetFuel)).elim
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
          cases site.instruction.symm.trans terminalAt
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
          · exact ⟨value, common + 1, bodyDone, bodyResult, ⟨_, wholeTrace⟩, by simpa [le, cx, envVars] using finalCells, finalDemand.operands⟩
          · exact (runtimeStep_excludes_return fallthrough.1 nextStep).elim

#print axioms accepted_generated_parameterized_callee_control_terminal
end Goose.Lower
