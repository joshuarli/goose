import Goose.Lower.DemandGeneratedBlockPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

structure GeneratedBlockPrefixEnd {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (map required : RetainedSsaMap) (cx : FnCtx)
    (results : List Ty) (before : LS) (loop : Option LoopCtx) (initial : GIR.Frame)
    (flow : Flow) (runtime : DemandRuntimePoint) : Prop where
  value : ∃ value, flow = .normal value ∧
    Post cfg env cx before initial (lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).2
      runtime.frame runtime.point [((lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).1, .val value)]
  result : BlockResult source flow runtime.state
  coverage : map.Covers required
  bounded : map.Bounded (lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).2.vals.size
  demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
    map.values map.runs runtime

structure GeneratedBlockPrefixDecomposition {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (map required : RetainedSsaMap) (before : LS) (loop : Option LoopCtx) (initial : GIR.Frame) (start : Pt)
    (cursor : DemandRuntimePoint → Prop) (taken : Nat) (reached : DemandRuntimePoint) : Prop where
  sourceOwner : GeneratedSourceOwner selected source.context
  coverage : map.Covers required
  progress : DemandPrefixDecomposition cx (fun fuel => execBlock fuel cfg env [] block) cursor
    (GeneratedBlockPrefixEnd source map required cx results before loop initial) taken ⟨start, initial, state⟩ reached

theorem accepted_generated_block_leave_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] true block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {fuel : Nat} {addressedState : St} {value : Val} {current : DemandRuntimePoint}
    (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1 } = .ok (.normal .unit) addressedState)
    (evaluated : valueFlow fuel cfg block.value { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      (.normal .unit) addressedState = .ok (.normal value) current.state)
    (post : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
      (lowerBlockValue true block.value (lowerEnv cfg.mod env.vars results)
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block)).2 current.frame current.point
      [((lowerBlockValue true block.value (lowerEnv cfg.mod env.vars results)
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block)).1, .val value)])
    (extended : ExtT (lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (demanded : GeneratedClearBlockDemand source map required cx results before loop initial current)
    {consumed taken : Nat} {reached : DemandRuntimePoint}
    (prefixSteps : DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ current)
    (residual : DemandRuntimePrefix cx taken current reached) :
    DemandPrefixDecomposition cx (fun fuel => execBlock fuel cfg env [] block)
      (GeneratedClearBlockDemand source map required cx results before loop initial)
      (GeneratedBlockPrefixEnd source map required cx results before loop initial)
      (consumed + taken) ⟨start, initial, state⟩ reached := by
  rcases residual.uncons with ⟨_, rfl⟩ | ⟨remaining, final, count, step, afterLeave⟩
  · exact .interior demanded
  · obtain ⟨_, _, _, _, evaluatedBlock, finalPost, finalResult, finalBounded, finalDemand⟩ :=
      accepted_generated_block_leave_runtime_step source occurrence rows coverage admitted bounded realized
        statements evaluated post extended step
    have valueId := generated_block_value_result (lowerEnv cfg.mod env.vars results) before loop [] true block
    have finalCells : Post cfg env cx before initial (lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).2
        final.frame final.point [((lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).1, .val value)] := by
      rw [valueId]; exact finalPost
    exact .complete (by omega) (prefixSteps.append (.next step (.zero final))) afterLeave evaluatedBlock
      ⟨⟨value, rfl, finalCells⟩, finalResult, coverage, finalBounded, finalDemand⟩

theorem accepted_generated_block_unit_suffix_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
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
    (residual : DemandRuntimePrefix cx taken addressed reached) :
    DemandPrefixDecomposition cx (fun fuel => execBlock fuel cfg env [] block)
      (GeneratedClearBlockDemand source map required cx results before loop initial)
      (GeneratedBlockPrefixEnd source map required cx results before loop initial)
      (consumed + taken) ⟨start, initial, state⟩ reached := by
  let le := lowerEnv cfg.mod env.vars results
  let valueStart := demandBlockValueBefore le before loop [] block
  let valueRun := lowerBlockValue true block.value le valueStart
  have unitSite : GeneratedBlockUnitInstruction cfg.mod body.rootsEnv.access cx.fn required
      ⟨body.path, .block, .exit⟩ addressed.point (.def valueRun.1 .constUnit) := by
    rw [show valueRun = emitDef .constUnit le valueStart from by dsimp [valueRun]; rw [noValue]; rfl]
    exact .unit bodyOccurrence bodyRows noValue post.pp extended
  have bodyResult := body.result fuel (.normal .unit) statements
  obtain ⟨finalTyping, _, sourceFrame, normal⟩ := bodyResult.frame
  have finalTypingEq := normal .unit rfl
  subst finalTyping
  have entryDemand : GeneratedClearBlockDemand source map required cx results before loop initial addressed :=
    .unitEntry canonical unitSite coverage ⟨⟨_, post.pp, post.rel⟩, sourceFrame, bodyRealized⟩
  rcases residual.uncons with ⟨_, rfl⟩ | ⟨remaining, middle, count, first, afterUnit⟩
  · exact .interior entryDemand
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
    have result := accepted_generated_block_leave_prefix source occurrence rows coverage admitted bounded realized
      statements valueDone unitPost extended leaveDemand (prefixSteps.append (.next first (.zero middle))) afterUnit
    have lengthEq : consumed + 1 + remaining = consumed + taken := by omega
    simpa only [lengthEq] using result

end Goose.Lower
