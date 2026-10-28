import Goose.Lower.DemandBranchBlockSuffix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive StoppedBranchBlockPrefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (map required : RetainedSsaMap) (cx : FnCtx) (results : List Ty)
    (before : LS) (initial : GIR.Frame) (start : Pt) (taken : Nat) (reached : DemandRuntimePoint)
    (stop : Stop) (after : St) : Prop
  | aborted (fuel : Nat) (evaluated : execBlock fuel cfg env [] block state = .stop stop after) :
      StoppedBranchBlockPrefix source map required cx results before initial start taken reached stop after
  | complete {fuel consumed remaining : Nat} {boundary : DemandRuntimePoint} {flow : Flow}
      (count : consumed + remaining = taken) (executed : DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ boundary)
      (residual : DemandRuntimePrefix cx remaining boundary reached)
      (evaluated : execBlock fuel cfg env [] block state = .ok flow boundary.state)
      (post : GeneratedBranchBlockEnd source map required cx results before none initial flow boundary) :
      StoppedBranchBlockPrefix source map required cx results before initial start taken reached stop after

inductive StoppedLoopBranchBlockPrefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (map required : RetainedSsaMap) (cx : FnCtx) (results : List Ty)
    (before : LS) (loop : Option LoopCtx) (initial : GIR.Frame) (start : Pt) (taken : Nat) (reached : DemandRuntimePoint)
    (stop : Stop) (after : St) : Prop
  | aborted (fuel : Nat) (evaluated : execBlock fuel cfg env [] block state = .stop stop after) :
      StoppedLoopBranchBlockPrefix source map required cx results before loop initial start taken reached stop after
  | complete {fuel consumed remaining : Nat} {boundary : DemandRuntimePoint} {flow : Flow}
      (count : consumed + remaining = taken) (executed : DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ boundary)
      (residual : DemandRuntimePrefix cx remaining boundary reached)
      (evaluated : execBlock fuel cfg env [] block state = .ok flow boundary.state)
      (post : GeneratedBranchBlockEnd source map required cx results before loop initial flow boundary) :
      StoppedLoopBranchBlockPrefix source map required cx results before loop initial start taken reached stop after

theorem accepted_generated_loop_branch_block_stopped {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock loop [] false block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (bodyFamily : GeneratedStoppedSequencePrefixFamily
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) cx results selected before loop [] false block block.stmts)
    (normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts innerState = .ok flow after →
      flow = .normal .unit) (noValue : block.value = none)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    StoppedLoopBranchBlockPrefix source map required cx results before loop initial start taken reached stop after := by
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
        ?_, input.counter.sameValues rfl enteredValues,
        bodyGenerated, bodyFrames⟩
      · apply input.metadata.transport
        · rw [bodyTyping]; exact source.same.impl
        · rw [bodyRoots]
      · apply input.loops.transport
        rw [bodyTyping]; exact source.same.loops
      · cases loop <;> exact input.targets
    have bodyProgress := bodyFamily body bodyOwned bodyOccurrence bodyAll bodyScope bodyValue bodyRows coverage bodyAdmitted
      (by rw [currentEq, enteredValues]; exact bounded) bodyDemand.operands bodyInput
      (by rw [currentEq]; exact generated_block_statements_extended extended) residual stopped nonTimeout
    cases bodyProgress with
    | aborted fuel done =>
      have raw : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts enteredState =
          .stop stop after := by
        change (execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts >>=
          prepareLoopFlow { env with scopes := (block.scope, state.nextScope) :: env.scopes } loop) enteredState = .stop stop after at done
        simp only [bind_apply] at done
        cases raw : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts enteredState with
        | stop reason final =>
          simp only [raw, Res.stop.injEq] at done
          obtain ⟨rfl, rfl⟩ := done
          rfl
        | ok flow final =>
          simp only [raw] at done
          have normal := normal raw
          subst flow
          cases loop <;> simp [prepareLoopFlow, prepareReturn, prepareLoopExit, pure_apply] at done
      apply StoppedLoopBranchBlockPrefix.aborted (fuel + 1)
      cases block with
      | mk scope statements value =>
        simp only [Core.Block.scope, Core.Block.stmts] at raw ⊢
        simp [execBlock, freshScope, bindAll, bind_apply, enteredState, raw]
    | @complete fuel consumed remaining boundary flow bodyCount bodySteps afterBody evaluated finished =>
      cases finished with
      | transfer abnormal post =>
        change (execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts >>=
          prepareLoopFlow { env with scopes := (block.scope, state.nextScope) :: env.scopes } loop) enteredState = .ok flow boundary.state at evaluated
        simp only [bind_apply] at evaluated
        cases raw : execStmts fuel cfg
            { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
            enteredState with
        | stop stop final => simp only [raw] at evaluated; cases evaluated
        | ok rawFlow rawState =>
          have normal := normal raw
          subst rawFlow
          simp only [raw] at evaluated
          have prepared : prepareLoopFlow { env with scopes := (block.scope, state.nextScope) :: env.scopes }
              loop (.normal .unit) rawState = .ok (.normal .unit) rawState := by cases loop <;> rfl
          rw [prepared] at evaluated
          exact (abnormal .unit (Res.ok.inj evaluated).1.symm).elim
      | normal bodyPost bodyResult bodyBounded bodyRealized =>
        have raw := preparedLoopFlow_normal_success evaluated
        rw [currentEq] at bodyPost bodyBounded
        have enteredPost : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before [] block)
            { initial with scopes := (block.scope, state.nextScope) :: initial.scopes } (start.1, start.2 + 1) [] :=
          ⟨bodyPoint, by simp, by simp, Nat.le_of_eq enteredValues.symm, fun _ _ => rfl, bodyRelated⟩
        obtain ⟨sourceFuel, total, rest, final, finalCount, finalSteps, finalResidual, sourceDone, finalBoundary⟩ :=
          accepted_generated_branch_leave_stopped source body canonical noValue occurrence rows
            coverage admitted bounded realized raw (enteredPost.comp bodyPost) bodyRealized extended
            (DemandRuntimePrefix.next enterStep bodySteps) afterBody stopped nonTimeout
        exact .complete (by omega) finalSteps finalResidual sourceDone finalBoundary


theorem accepted_generated_generic_branch_block_stopped {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block none [] false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock none [] false block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (bodyFamily : GeneratedStoppedSequencePrefixFamily
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) cx results selected before none [] false block block.stmts)
    (normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts innerState = .ok flow after →
      flow = .normal .unit) (noValue : block.value = none)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    StoppedBranchBlockPrefix source map required cx results before initial start taken reached stop after := by
  have result := accepted_generated_loop_branch_block_stopped source selected owned occurrence rows coverage admitted bounded realized input extended
    bodyFamily normal noValue steps stopped nonTimeout
  cases result with
  | aborted fuel evaluated => exact .aborted fuel evaluated
  | complete count executed residual evaluated post => exact .complete count executed residual evaluated post


theorem accepted_generated_scalar_loop_branch_block_stopped {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock loop [] false block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (fragment : ScalarAssignmentStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts) (noValue : block.value = none)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    StoppedLoopBranchBlockPrefix source map required cx results before loop initial start taken reached stop after := by
  have bodyFamily : GeneratedStoppedSequencePrefixFamily
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) cx results selected before loop [] false block block.stmts :=
    (accepted_generated_scalar_assignment_statements_agreement
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) selected before loop [] false block fragment).2
  exact accepted_generated_loop_branch_block_stopped source selected owned occurrence rows coverage admitted bounded realized input extended
    bodyFamily (fun done => fragment.normal done) noValue steps stopped nonTimeout


theorem accepted_generated_scalar_branch_block_stopped {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block none [] false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock none [] false block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (fragment : ScalarAssignmentStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts) (noValue : block.value = none)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    StoppedBranchBlockPrefix source map required cx results before initial start taken reached stop after := by
  have bodyFamily : GeneratedStoppedSequencePrefixFamily
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) cx results selected before none [] false block block.stmts :=
    (accepted_generated_scalar_assignment_statements_agreement
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) selected before none [] false block fragment).2
  exact accepted_generated_generic_branch_block_stopped source selected owned occurrence rows coverage admitted bounded realized input extended
    bodyFamily (fun done => fragment.normal done) noValue steps stopped nonTimeout

#print axioms accepted_generated_loop_branch_block_stopped
#print axioms accepted_generated_scalar_loop_branch_block_stopped
#print axioms accepted_generated_scalar_branch_block_stopped
end Goose.Lower
