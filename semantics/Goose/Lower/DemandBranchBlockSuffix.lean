import Goose.Lower.DemandBranchBlockStatements
import Goose.Lower.DemandGeneratedBlockLeave

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

structure GeneratedBranchBlockEnd {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (map required : RetainedSsaMap) (cx : FnCtx)
    (results : List Ty) (before : LS) (loop : Option LoopCtx) (initial : GIR.Frame)
    (flow : Flow) (runtime : DemandRuntimePoint) : Prop where
  normal : flow = .normal .unit
  post : Post cfg env cx before initial (lowerBlock loop [] false block (lowerEnv cfg.mod env.vars results) before).2
    runtime.frame runtime.point []
  result : BlockResult source flow runtime.state
  bounded : map.Bounded (lowerBlock loop [] false block (lowerEnv cfg.mod env.vars results) before).2.vals.size
  demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
    map.values map.runs runtime

theorem accepted_generated_branch_leave_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    (body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1 })
    (canonical : GeneratedBlockBodyAt source body) (noValue : block.value = none)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {fuel : Nat} {current : DemandRuntimePoint}
    (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1 } = .ok (.normal .unit) current.state)
    (post : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block) current.frame current.point [])
    (bodyRealized : map.Realizes cfg.mod body.world { env with scopes := (block.scope, state.nextScope) :: env.scopes } current)
    (extended : ExtT (lowerBlock loop [] false block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {consumed taken : Nat} {reached : DemandRuntimePoint}
    (prefixSteps : DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ current)
    (residual : DemandRuntimePrefix cx taken current reached) :
    DemandPrefixDecomposition cx (fun fuel => execBlock fuel cfg env [] block)
      (GeneratedBranchBlockEffectDemand source map required cx results before loop initial)
      (GeneratedBranchBlockEnd source map required cx results before loop initial)
      (consumed + taken) ⟨start, initial, state⟩ reached := by
  have bodyResult := body.result fuel (.normal .unit) statements
  obtain ⟨typingFinal, same, frame, finalTyping⟩ := bodyResult.frame
  have typingEq := finalTyping .unit rfl
  subst typingFinal
  have valuePost : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
      (lowerBlockValue false block.value (lowerEnv cfg.mod env.vars results)
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block)).2 current.frame current.point [] := by
    simpa only [noValue, lowerBlockValue, Bool.false_eq_true, ite_false, pure_run] using post

  have leaveSite := GeneratedDemandInstruction.blockLeave_auto occurrence rows valuePost.pp extended
  have leaveLabel : (match block.value with
      | some _ => (⟨source.path ++ [block.stmts.length], .expression, .exit⟩ : DemandSourceLabel)
      | none => ⟨source.path, .block, .exit⟩) = ⟨source.path, .block, .exit⟩ := by rw [noValue]
  have demanded : GeneratedClearBlockDemand source map required cx results before loop initial current :=
    .leave canonical (leaveLabel ▸ leaveSite) coverage ⟨⟨_, post.pp, post.rel⟩, frame, bodyRealized⟩
  rcases residual.uncons with ⟨_, rfl⟩ | ⟨remaining, final, _, step, afterLeave⟩
  · exact .interior ⟨demanded, _, leaveSite.instruction⟩
  · have valueDone : valueFlow fuel cfg block.value
        { env with scopes := (block.scope, state.nextScope) :: env.scopes } (.normal .unit) current.state =
        .ok (.normal .unit) current.state := by rw [noValue]; rfl
    obtain ⟨_, _, _, _, evaluated, finalPost, finalResult, finalBounded, finalDemand⟩ :=
      accepted_generated_block_leave_runtime_step source occurrence rows coverage admitted bounded realized
        statements valueDone valuePost extended step
    exact .complete (by omega) (prefixSteps.append (.next step (.zero _))) afterLeave evaluated
      ⟨rfl, finalPost, finalResult, finalBounded, finalDemand⟩

theorem accepted_generated_branch_leave_stopped {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    (body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1 })
    (canonical : GeneratedBlockBodyAt source body) (noValue : block.value = none)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {fuel : Nat} {current : DemandRuntimePoint}
    (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1 } = .ok (.normal .unit) current.state)
    (post : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block) current.frame current.point [])
    (bodyRealized : map.Realizes cfg.mod body.world { env with scopes := (block.scope, state.nextScope) :: env.scopes } current)
    (extended : ExtT (lowerBlock loop [] false block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {consumed taken : Nat} {reached : DemandRuntimePoint}
    (prefixSteps : DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ current)
    (residual : DemandRuntimePrefix cx taken current reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    ∃ sourceFuel total remaining boundary,
      total + remaining = consumed + taken ∧ DemandRuntimePrefix cx total ⟨start, initial, state⟩ boundary ∧
      DemandRuntimePrefix cx remaining boundary reached ∧
      execBlock sourceFuel cfg env [] block state = .ok (.normal .unit) boundary.state ∧
      GeneratedBranchBlockEnd source map required cx results before loop initial (.normal .unit) boundary := by
  have valuePost : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
      (lowerBlockValue false block.value (lowerEnv cfg.mod env.vars results)
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block)).2 current.frame current.point [] := by
    simpa only [noValue, lowerBlockValue, Bool.false_eq_true, ite_false, pure_run] using post
  have leaveSite := GeneratedDemandInstruction.blockLeave_auto occurrence rows valuePost.pp extended
  rcases residual.uncons with ⟨_, rfl⟩ | ⟨remaining, final, count, step, afterLeave⟩
  · have expected : DemandInstructionStep cx targetFuel reached
        ⟨(reached.point.1, reached.point.2 + 1), { reached.frame with scopes := env.scopes },
          { reached.state with store := releaseVars env.vars env.act block.scope state.nextScope env.vars.size reached.state.store }⟩ := by
      apply DemandInstructionStep.effect leaveSite.instruction
      exact block_leave_exec valuePost.rel reached.state
    exact (stopped.excludes_step_nonTimeout nonTimeout expected).elim
  · have valueDone : valueFlow fuel cfg block.value
        { env with scopes := (block.scope, state.nextScope) :: env.scopes } (.normal .unit) current.state =
        .ok (.normal .unit) current.state := by rw [noValue]; rfl
    obtain ⟨_, _, _, _, evaluated, finalPost, finalResult, finalBounded, finalDemand⟩ :=
      accepted_generated_block_leave_runtime_step source occurrence rows coverage admitted bounded realized
        statements valueDone valuePost extended step
    exact ⟨fuel + 1, consumed + 1, remaining, final, by omega,
      by simpa [Nat.add_comm] using prefixSteps.append (.next step (.zero _)), afterLeave, evaluated,
      ⟨rfl, finalPost, finalResult, finalBounded, finalDemand⟩⟩

structure GeneratedBranchBlockDecomposition {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (map required : RetainedSsaMap) (before : LS) (loop : Option LoopCtx) (initial : GIR.Frame) (start : Pt)
    (taken : Nat) (reached : DemandRuntimePoint) : Prop where
  sourceOwner : GeneratedSourceOwner selected source.context
  coverage : map.Covers required
  progress : DemandPrefixDecomposition cx (fun fuel => execBlock fuel cfg env [] block)
    (GeneratedScalarAssignmentBlockPrefixDemand source selected map required before loop initial
      (GeneratedBranchBlockEffectDemand source map required cx results before loop initial))
    (GeneratedBranchBlockEnd source map required cx results before loop initial) taken ⟨start, initial, state⟩ reached


structure GeneratedGenericBranchBlockDecomposition {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (map required : RetainedSsaMap) (before : LS) (loop : Option LoopCtx) (initial : GIR.Frame) (start : Pt)
    (cursor : ∀ {statement : Stmt} {innerState : St}, StmtSource cfg
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } statement innerState →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (taken : Nat) (reached : DemandRuntimePoint) : Prop where
  sourceOwner : GeneratedSourceOwner selected source.context
  coverage : map.Covers required
  progress : DemandPrefixDecomposition cx (fun fuel => execBlock fuel cfg env [] block)
    (GeneratedGenericBlockPrefixDemand source selected map required before loop initial cursor
      (GeneratedBranchBlockEffectDemand source map required cx results before loop initial))
    (GeneratedBranchBlockEnd source map required cx results before loop initial) taken ⟨start, initial, state⟩ reached

theorem accepted_generated_invariant_branch_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    {before : LS} {loop : Option LoopCtx}
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
    (cursor : ∀ {statement : Stmt} {innerState : St}, StmtSource cfg
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } statement innerState →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (invariant : DemandRuntimePoint → Prop)
    (advance : ∀ {length : Nat} {first last : DemandRuntimePoint}, invariant first → DemandRuntimePrefix cx length first last → invariant last)
    (atStart : invariant ⟨start, initial, state⟩)
    (bodyFamily : InvariantSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before loop [] false block block.stmts cursor invariant)
    (normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts innerState = .ok flow after →
      flow = .normal .unit)
    (noValue : block.value = none)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedGenericBranchBlockDecomposition source selected map required before loop initial start cursor taken reached := by
  refine ⟨owned, coverage, ?_⟩
  have progress := accepted_generated_invariant_block_statements_prefix source selected owned occurrence rows coverage admitted bounded
    realized input extended _ invariant advance atStart bodyFamily steps
  rcases progress with ⟨_, rfl, entry⟩ | progressed
  · have site := GeneratedDemandInstruction.blockEnter_auto occurrence rows input.atPoint extended
    exact .interior (.emitted entry ⟨_, site.instruction⟩)
  · cases progressed with
    | intro body canonical bodyOccurrence bodyRows remaining count enterStep _bodyInput bodyProgress =>
      cases bodyProgress.progress with
      | interior demanded => exact .interior (.body canonical demanded)
      | @complete sourceFuel consumed residualLength boundary flow bodyCount bodySteps residual evaluated finished =>
        cases finished with
        | transfer abnormal post =>
          simp only [bind_apply] at evaluated
          cases raw : execStmts sourceFuel cfg
              { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
              { state with nextScope := state.nextScope + 1 } with
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
          have currentEq : (lowerStmts loop (block.stmts.take body.offset) (lowerEnv cfg.mod env.vars results)
              (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before [] block)).2 =
              demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before [] block := by
            simp only [canonical.offset, List.take_zero, lowerStmts, pure_run]
          rw [currentEq] at bodyPost bodyBounded
          have enteredValues : (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before [] block).vals.size = before.vals.size := by
            have values := (emitEffect_facts (show emitEffect (.enter block.scope) (lowerEnv cfg.mod env.vars results) before =
              ((emitEffect (.enter block.scope) (lowerEnv cfg.mod env.vars results) before).1,
               (emitEffect (.enter block.scope) (lowerEnv cfg.mod env.vars results) before).2) from rfl)
              input.atPoint (generated_block_enter_extended extended)).1
            simpa only [demandBlockStatementsBefore, initSlots, pure_run] using values
          obtain ⟨_, _, _, _, _, _, _, enterPoint, enterRelated, _, _⟩ :=
            accepted_generated_block_enter_runtime_step source occurrence rows coverage bounded input.atPoint input.related realized extended enterStep
          have enteredPost : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
              (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before [] block)
              { initial with scopes := (block.scope, state.nextScope) :: initial.scopes } (start.1, start.2 + 1) [] :=
            ⟨enterPoint, by simp, by simp, Nat.le_of_eq enteredValues.symm, fun _ _ => rfl, enterRelated⟩
          have suffix := accepted_generated_branch_leave_prefix source body canonical noValue occurrence rows
            coverage admitted bounded realized raw (enteredPost.comp bodyPost) bodyRealized extended
            (DemandRuntimePrefix.next enterStep bodySteps) residual
          cases suffix with
          | interior demanded => exact .interior (.suffix demanded)
          | complete suffixCount prefixSteps residual evaluated post =>
            exact .complete (by omega) prefixSteps residual evaluated post


theorem accepted_generated_generic_branch_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    {before : LS} {loop : Option LoopCtx}
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
    (cursor : ∀ {statement : Stmt} {innerState : St}, StmtSource cfg
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } statement innerState →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (bodyFamily : GeneratedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before loop [] false block block.stmts cursor)
    (normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts innerState = .ok flow after →
      flow = .normal .unit)
    (noValue : block.value = none)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedGenericBranchBlockDecomposition source selected map required before loop initial start cursor taken reached := by
  have family : InvariantSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before loop [] false block block.stmts cursor (fun _ => True) := by
    intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
    exact bodyFamily source owned occurrence all scope value rows coverage admitted bounded realized input extended steps
  exact accepted_generated_invariant_branch_block_prefix source selected owned occurrence rows coverage admitted bounded realized input extended
    cursor (fun _ => True) (fun _ _ => trivial) trivial family normal noValue steps

theorem accepted_generated_scalar_branch_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (fragment : ScalarAssignmentStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    {before : LS} {loop : Option LoopCtx}
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
    (noValue : block.value = none)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedBranchBlockDecomposition source selected map required before loop initial start taken reached := by
  have bodyFamily : GeneratedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before loop [] false block block.stmts
      (@ScalarAssignmentStatementPrefixCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results) :=
    (accepted_generated_scalar_assignment_statements_agreement
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      selected before loop [] false block fragment).1
  have result := accepted_generated_generic_branch_block_prefix source selected owned occurrence rows coverage admitted bounded realized input extended
    _ bodyFamily (fun done => fragment.normal done) noValue steps
  refine ⟨result.sourceOwner, result.coverage, ?_⟩
  cases result.progress with
  | interior demanded =>
    cases demanded with
    | emitted cursor instruction => exact .interior (.emitted cursor)
    | suffix cursor => exact .interior (.suffix cursor)
    | body canonical cursor => exact .interior (.body canonical cursor)
  | complete count executed residual evaluated post => exact .complete count executed residual evaluated post


#print axioms accepted_generated_scalar_branch_block_prefix
#print axioms accepted_generated_branch_leave_stopped

#print axioms accepted_generated_branch_leave_prefix
end Goose.Lower
