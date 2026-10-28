import Goose.Lower.DemandCallBodyStopped
import Goose.Lower.DemandCallBoolBodyReturn

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_parameterized_callee_literal_stopped {cfg : Cfg} {ctx : Context} {impl : Impl} {env : Env}
    {pre : List (VarId × Val)} {state : St} (source : BlockSource cfg env pre impl.body state)
    (envVars : env.vars = impl.vars)
    (fragment : WhileMixedStatements cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } impl.body.stmts)
    {expression : Expr} {value : Val} {operation : Op}
    (literal : CallScalarLiteral expression value operation) (hasValue : impl.body.value = some expression)
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
  obtain ⟨body, bodyOffset, progress, bodyReached⟩ :=
    accepted_generated_parameterized_mixed_body_stopped source fragment selected owned occurrence rows coverage admitted bounded cells realized input extended entry
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
      let valueId := (lowerExpr expression le valueStart).1
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, prologuePost, _⟩ :=
        accepted_generated_post_prologue source selected owned occurrence rows coverage admitted bounded cells realized input extended entry
      have wholeStatements : Post cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } cx
          (callEntry impl) initial valueStart boundary.frame boundary.point [] := by
        simpa [valueStart, demandBlockValueBefore] using prologuePost.comp nextPost
      have valueExtended : ExtT (lowerExpr expression le valueStart).2 cx.fn.blocks := by
        simpa [hasValue, lowerBlockValue, valueStart] using generated_block_value_extended extended
      have emit : emitDef operation le valueStart =
          ((lowerExpr expression le valueStart).1, (lowerExpr expression le valueStart).2) := by cases literal <;> rfl
      obtain ⟨valuePost, valueInstruction⟩ := Post.def_leaf wholeStatements emit valueExtended (.val value)
      let valuePoint : DemandRuntimePoint := ⟨(boundary.point.1, boundary.point.2 + 1), boundary.frame.set valueId (.val value), boundary.state⟩
      have valueStep : RuntimeStep cx.cfg cx.fn boundary.point boundary.frame boundary.state valuePoint.point valuePoint.frame valuePoint.state := by
        dsimp [valuePoint, valueId]
        apply RuntimeStep.define (fuel := 0) valueInstruction
        cases literal <;> simp [execOp, execPure, pure_apply]
      rcases residual.uncons with ⟨_, same⟩ | ⟨rest, actualValue, length, first, afterValue⟩
      · subst terminal
        have expected : DemandInstructionStep cx targetFuel boundary valuePoint := by
          apply DemandInstructionStep.definition valueInstruction
          cases literal <;> simp [execOp, execPure, pure_apply, valuePoint, valueId]
        exact (stopped.excludes_step_nonTimeout nonTimeout expected).elim
      · obtain ⟨firstFuel, firstInstruction⟩ := runtimeStep_demandInstructionStep first
        obtain ⟨valueFuel, expectedInstruction⟩ := runtimeStep_demandInstructionStep valueStep
        have same := firstInstruction.deterministic_across_fuel expectedInstruction
        have actualEq : actualValue = valuePoint :=
          (show actualValue = ⟨actualValue.point, actualValue.frame, actualValue.state⟩ from by cases actualValue; rfl).trans
            (same.trans (show ⟨valuePoint.point, valuePoint.frame, valuePoint.state⟩ = valuePoint from by cases valuePoint; rfl))
        subst actualValue
        let common : Nat := max sourceFuel 1
        have statementsRaised := ((Goose.Proofs.Fuel.monoAll sourceFuel common (by dsimp [common]; omega)).stmts cfg
          { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } impl.body.stmts
          { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }).1 _ _ statements
        have valueDone : valueFlow common cfg impl.body.value
            { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } (.normal .unit) boundary.state =
            .ok (.normal value) boundary.state := by
          rw [hasValue]
          have positive : 0 < common := by dsimp [common]; omega
          obtain ⟨n, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
          rw [fuelEq]
          cases literal <;> simp [valueFlow, evalExpr, bind_apply, pure_apply]
        have wholeValue : Post cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } cx
            (callEntry impl) initial (lowerBlockValue false impl.body.value le valueStart).2 valuePoint.frame valuePoint.point
            [((lowerBlockValue false impl.body.value le valueStart).1, .val value)] := by
          simpa [hasValue, lowerBlockValue, valuePoint, valueId] using valuePost
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

theorem accepted_generated_parameterized_callee_bool_stopped {cfg : Cfg} {ctx : Context} {impl : Impl} {env : Env}
    {pre : List (VarId × Val)} {state : St} (source : BlockSource cfg env pre impl.body state)
    (envVars : env.vars = impl.vars)
    (fragment : WhileMixedStatements cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } impl.body.stmts)
    {boolean : Bool} (hasValue : impl.body.value = some (.bool boolean))
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
  exact accepted_generated_parameterized_callee_literal_stopped source envVars fragment (.boolean boolean) hasValue selected owned occurrence rows
    coverage admitted bounded cells realized input entry steps stopped nonTimeout

#print axioms accepted_generated_parameterized_callee_literal_stopped
#print axioms accepted_generated_parameterized_callee_bool_stopped
end Goose.Lower
