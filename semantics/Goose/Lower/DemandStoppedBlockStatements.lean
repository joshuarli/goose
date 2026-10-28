import Goose.Lower.DemandControlStatementAgreement

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem ControlStatements.normal {statements : List Stmt} (fragment : ControlStatements statements)
    {cfg : Cfg} {env : Env} {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env statements state = .ok flow after) : flow = .normal .unit := by
  induction fragment generalizing fuel state after with
  | nil =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, pure_apply, Res.ok.injEq] at done
      exact done.1.symm
  | clear global origin tail ih =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, bind_apply] at done
      cases head : execStmt fuel cfg env (.clear (.global global) origin) state with
      | stop stop final => simp only [head] at done; cases done
      | ok headFlow middle =>
        obtain ⟨rfl, _⟩ := global_clear_source head
        simp only [head] at done
        exact ih done
  | @expression expression origin form rest tail ih =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, bind_apply] at done
      cases head : execStmt fuel cfg env (.expr expression origin) state with
      | stop stop final => simp only [head] at done; cases done
      | ok headFlow middle =>
        have normal : headFlow = .normal .unit := by
          cases fuel with
          | zero => simp [execStmt, timeout, M.stop] at head
          | succ fuel =>
            simp only [execStmt, bind_apply] at head
            cases evaluated : evalExpr fuel cfg env expression state with
            | stop stop final => simp only [evaluated] at head; cases head
            | ok value final => simp only [evaluated, pure_apply, Res.ok.injEq] at head; exact head.1.symm
        subst headFlow
        simp only [head] at done
        exact ih done

theorem accepted_generated_block_statements_stopped {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block none [] true block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock none [] true block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (fragment : ControlStatements block.stmts)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    (∃ fuel, execBlock fuel cfg env [] block state = .stop stop after) ∨
      ∃ bodyFuel consumed remaining boundary flow,
          consumed + remaining + 1 = taken ∧
          DemandRuntimePrefix cx consumed
            ⟨(start.1, start.2 + 1), { initial with scopes := (block.scope, state.nextScope) :: initial.scopes },
              { state with nextScope := state.nextScope + 1 }⟩ boundary ∧
          DemandRuntimePrefix cx remaining boundary reached ∧
          (execStmts bodyFuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts >>=
            prepareLoopFlow { env with scopes := (block.scope, state.nextScope) :: env.scopes } none)
            { state with nextScope := state.nextScope + 1 } = .ok flow boundary.state := by
  let loop : Option LoopCtx := none
  let le := lowerEnv cfg.mod env.vars results
  let enteredFrame : GIR.Frame := { initial with scopes := (block.scope, state.nextScope) :: initial.scopes }
  let enteredState : St := { state with nextScope := state.nextScope + 1 }
  let enteredPoint : Pt := (start.1, start.2 + 1)
  let bodyBefore := demandBlockStatementsBefore le before [] block
  have enterSite := GeneratedDemandInstruction.blockEnter_auto occurrence rows input.atPoint extended
  have enterRun : execEff cx.fn initial (.enter block.scope) state = .ok enteredFrame enteredState := by
    simp only [execEff, freshScope, bind_apply, pure_apply, enteredFrame, enteredState]
  have enterStep : Evidence.RuntimeStep cx.cfg cx.fn start initial state enteredPoint enteredFrame enteredState :=
    .effect enterSite.instruction enterRun
  obtain ⟨_, entryDemand, _, _, _, _, _, bodyPoint, bodyRelated, _, _⟩ :=
    accepted_generated_block_enter_runtime_step source occurrence rows coverage bounded input.atPoint input.related realized extended enterStep
  rcases steps.uncons with ⟨zero, rfl⟩ | ⟨remaining, middle, count, first, residual⟩
  · exact (stopped.excludes_step_nonTimeout nonTimeout (DemandInstructionStep.effect (fuel := targetFuel) enterSite.instruction enterRun)).elim
  · obtain ⟨fuel, first⟩ := runtimeStep_demandInstructionStep first
    have expected : DemandInstructionStep cx fuel ⟨start, initial, state⟩ ⟨enteredPoint, enteredFrame, enteredState⟩ :=
      .effect enterSite.instruction enterRun
    have same := first.deterministic expected
    have middleEq : middle = ⟨enteredPoint, enteredFrame, enteredState⟩ :=
      (show middle = ⟨middle.point, middle.frame, middle.state⟩ from by cases middle; rfl).trans same
    subst middle
    obtain ⟨body, bodyTyping, bodyTypingAfter, bodyRoots, bodyWorld, _, _, bodyTypingEnd, _, bodyRootsEnd,
      bodyPlans, bodyPath, bodyScope, bodyAll, bodyValue, bodyOffset, bodyContext,
      bodyOccurrence, bodyRows, _, bodyAdmitted, _, bodyDemand⟩ :=
      accepted_generated_body_entry source occurrence rows coverage admitted (show PreRel initial [] [] from trivial)
        realized bodyPoint bodyRelated
    have canonical : GeneratedBlockBodyAt source body :=
      ⟨bodyWorld, bodyPlans, bodyPath, bodyScope, bodyAll, bodyValue, bodyOffset, bodyContext,
        bodyRoots, bodyTypingAfter, bodyTypingEnd, bodyRootsEnd⟩
    have bodyOwned : GeneratedSourceOwner selected body.context :=
      owned.transport bodyPlans.symm bodyPath.symm (by rw [bodyScope, bodyAll, bodyValue]; cases block; rfl) bodyContext.symm
    have currentEq : (lowerStmts loop (block.stmts.take body.offset) le bodyBefore).2 = bodyBefore := by
      simp only [bodyOffset, List.take_zero, lowerStmts, pure_run]
    have enteredValues : bodyBefore.vals.size = before.vals.size := by
      have values := (emitEffect_facts (show emitEffect (.enter block.scope) le before =
        ((emitEffect (.enter block.scope) le before).1, (emitEffect (.enter block.scope) le before).2) from rfl)
        input.atPoint (generated_block_enter_extended extended)).1
      simpa only [bodyBefore, demandBlockStatementsBefore, initSlots, pure_run] using values
    have generatedEntered := input.generated.emitEffect (.enter block.scope)
      (show emitEffect (.enter block.scope) le before =
        ((emitEffect (.enter block.scope) le before).1, (emitEffect (.enter block.scope) le before).2) from rfl)
    have bodyGenerated : GeneratedBuilderState bodyBefore :=
      ⟨generatedEntered.dense, generatedEntered.live, generatedEntered.targets⟩
    have bodyFrames : LoopBuilderFrames loop bodyBefore :=
      input.frames.mono (adv_emitEffect (show emitEffect (.enter block.scope) le before =
        ((emitEffect (.enter block.scope) le before).1, (emitEffect (.enter block.scope) le before).2) from rfl)).ext
    have bodyInput : GeneratedPrefixInput cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx results loop body.typingEnv body.rootsEnv
        (lowerStmts loop (block.stmts.take body.offset) le bodyBefore).2 enteredFrame enteredPoint := by
      rw [currentEq]
      refine ⟨?_, ?_, bodyPoint, bodyRelated, input.moduleEq, input.resultsEq,
        loopDepthFits_entered block.scope state.nextScope input.depth,
        input.targets, input.counter.sameValues rfl enteredValues,
        bodyGenerated, bodyFrames⟩
      · apply input.metadata.transport
        · rw [bodyTyping]; exact source.same.impl
        · rw [bodyRoots]
      · apply input.loops.transport
        rw [bodyTyping]; exact source.same.loops
    have bodyFamily : GeneratedStoppedSequencePrefixFamily
        (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) cx results selected before none [] true block block.stmts := by
      intro bodyState
      exact accepted_generated_control_statements_stopped
        (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
        selected before none [] true block fragment.stopped
    have bodyProgress := bodyFamily body bodyOwned bodyOccurrence bodyAll bodyScope bodyValue bodyRows coverage bodyAdmitted
      (by rw [currentEq, enteredValues]; exact bounded) bodyDemand.operands bodyInput
      (by rw [currentEq]; exact generated_block_statements_extended extended) residual stopped nonTimeout
    cases bodyProgress with
    | aborted fuel done =>
      have raw : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts enteredState =
          .stop stop after := by
        change (execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts >>=
          prepareLoopFlow { env with scopes := (block.scope, state.nextScope) :: env.scopes } none) enteredState = .stop stop after at done
        simp only [bind_apply] at done
        cases raw : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts enteredState with
        | stop reason final =>
          simp only [raw, Res.stop.injEq] at done
          obtain ⟨rfl, rfl⟩ := done
          rfl
        | ok flow final =>
          simp only [raw] at done
          have normal := fragment.normal raw
          subst flow
          simp [prepareLoopFlow, prepareReturn, pure_apply] at done
      left
      refine ⟨fuel + 1, ?_⟩
      cases block with
      | mk scope statements value =>
        simp only [Core.Block.scope, Core.Block.stmts] at raw ⊢
        simp [execBlock, freshScope, bindAll, bind_apply, enteredState, raw]
    | @complete fuel consumed remaining boundary flow count prefixSteps remainingSteps done final =>
      right
      exact ⟨fuel, consumed, remaining, boundary, flow, by omega, prefixSteps, remainingSteps, done⟩

#print axioms accepted_generated_block_statements_stopped

end Goose.Lower
