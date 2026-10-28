import Goose.Lower.DemandControlBlockPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_unit_block_suffix_stopped {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    (body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1 })
    (canonical : GeneratedBlockBodyAt source body) (noValue : block.value = none)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] true block) before)
    (bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root body.path (.block loop [] true block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (bodyRows : GeneratedDemandRows cfg.mod body.rootsEnv.access bodyOccurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {fuel : Nat} {addressed : DemandRuntimePoint}
    (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1 } = .ok (.normal .unit) addressed.state)
    (post : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block) addressed.frame addressed.point [])
    (bodyBounded : map.Bounded (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block).vals.size)
    (bodyRealized : map.Realizes cfg.mod body.world { env with scopes := (block.scope, state.nextScope) :: env.scopes } addressed)
    (extended : ExtT (lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {consumed taken : Nat} {reached : DemandRuntimePoint}
    (prefixSteps : DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ addressed)
    (residual : DemandRuntimePrefix cx taken addressed reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    ∃ sourceFuel total remaining boundary flow, total + remaining = consumed + taken ∧
      DemandRuntimePrefix cx total ⟨start, initial, state⟩ boundary ∧
      DemandRuntimePrefix cx remaining boundary reached ∧
      execBlock sourceFuel cfg env [] block state = .ok flow boundary.state ∧
      GeneratedBlockPrefixEnd source map required cx results before loop initial flow boundary := by
  let le := lowerEnv cfg.mod env.vars results
  let valueStart := demandBlockValueBefore le before loop [] block
  let valueRun := lowerBlockValue true block.value le valueStart
  have unitSite : GeneratedBlockUnitInstruction cfg.mod body.rootsEnv.access cx.fn required
      ⟨body.path, .block, .exit⟩ addressed.point (.def valueRun.1 .constUnit) := by
    rw [show valueRun = emitDef .constUnit le valueStart from by dsimp [valueRun]; rw [noValue]; rfl]
    exact .unit bodyOccurrence bodyRows noValue post.pp extended
  rcases residual.uncons with ⟨_, rfl⟩ | ⟨remaining, middle, count, first, afterUnit⟩
  · cases stopped with
    | timeout => exact (nonTimeout rfl).elim
    | definition instruction execution =>
      cases unitSite.instruction.symm.trans instruction
      simp only [execOp, execPure, pure_apply, reduceCtorEq] at execution
    | effect instruction execution => cases unitSite.instruction.symm.trans instruction
  · obtain ⟨_, _, _, _, _, unitState, unitPost, unitDemand⟩ := accepted_generated_block_unit_runtime_step body statements
      bodyOccurrence canonical.all canonical.scope canonical.value noValue bodyRows coverage post bodyBounded bodyRealized extended first
    have leaveSite := GeneratedDemandInstruction.blockLeave_auto occurrence rows unitPost.pp extended
    have leaveLabel : (match block.value with
        | some _ => (⟨source.path ++ [block.stmts.length], .expression, .exit⟩ : DemandSourceLabel)
        | none => ⟨source.path, .block, .exit⟩) = ⟨source.path, .block, .exit⟩ := by rw [noValue]
    have leaveDemand : GeneratedClearBlockDemand source map required cx results before loop initial middle :=
      .leave canonical (leaveLabel ▸ leaveSite) coverage unitDemand
    have valueDone : valueFlow fuel cfg block.value
        { env with scopes := (block.scope, state.nextScope) :: env.scopes } (.normal .unit) addressed.state =
        .ok (.normal .unit) middle.state := by rw [noValue, unitState]; rfl
    rcases afterUnit.uncons with ⟨_, rfl⟩ | ⟨rest, final, countLeave, step, afterLeave⟩
    · have expected : DemandInstructionStep cx targetFuel reached
          ⟨(reached.point.1, reached.point.2 + 1), { reached.frame with scopes := env.scopes },
            { reached.state with store := releaseVars env.vars env.act block.scope state.nextScope env.vars.size reached.state.store }⟩ := by
        apply DemandInstructionStep.effect leaveSite.instruction
        exact block_leave_exec unitPost.rel reached.state
      exact (stopped.excludes_step_nonTimeout nonTimeout expected).elim
    · obtain ⟨_, _, _, _, evaluatedBlock, finalPost, finalResult, finalBounded, finalDemand⟩ :=
        accepted_generated_block_leave_runtime_step source occurrence rows coverage admitted bounded realized
          statements valueDone unitPost extended step
      have valueId := generated_block_value_result le before loop [] true block
      have finalCells : Post cfg env cx before initial (lowerBlock loop [] true block le before).2
          final.frame final.point [((lowerBlock loop [] true block le before).1, .val .unit)] := by
        rw [valueId]
        exact finalPost
      refine ⟨fuel + 1, consumed + 2, rest, final, .normal .unit, by omega, ?_, afterLeave, evaluatedBlock,
        ⟨⟨.unit, rfl, finalCells⟩, finalResult, coverage, finalBounded, finalDemand⟩⟩
      have tail := DemandRuntimePrefix.next first (.next step (.zero final))
      simpa only [Nat.add_assoc] using prefixSteps.append tail

#print axioms accepted_generated_unit_block_suffix_stopped

end Goose.Lower
