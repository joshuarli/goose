import Goose.Lower.DemandGeneratedConstruction
import Goose.Lower.DemandScopeCarried
import Goose.Evidence.Execution

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_block_enter_runtime_step {cfg : Cfg} {env : Env}
    {pre : List (VarId × Val)} {block : Core.Block} {state after : St}
    (source : BlockSource cfg env pre block state) {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop bindings want block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (bounded : map.Bounded before.vals.size)
    {frame : GIR.Frame} {point : Pt} (atPoint : before.pp = some point)
    (related : Rel cfg env cx frame before)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (extended : ExtT (lowerBlock loop bindings want block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame state next nextFrame after) :
    GeneratedDemandInstruction cfg.mod source.rootsEnv.access cx.fn required ⟨source.path, .block, .entry⟩ point (.eff (.enter block.scope)) ∧
      DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.inputFuture
        map.values map.runs ⟨point, frame, state⟩ ∧
    ∃ cursor : ParameterPrefixCursor source 0, map.Covers required ∧ next = (point.1, point.2 + 1) ∧
      nextFrame = { frame with scopes := (block.scope, state.nextScope) :: frame.scopes } ∧
      after = { state with nextScope := state.nextScope + 1 } ∧
      map.Bounded (emitEffect (.enter block.scope) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx source.world
        cursor.typing { source.rootsEnv with scopes := block.scope :: source.rootsEnv.scopes }
        source.context.inputFuture map.values map.runs ⟨next, nextFrame, after⟩ := by
  have site := GeneratedDemandInstruction.blockEnter_auto occurrence rows atPoint extended
  refine ⟨site, ⟨⟨before, atPoint, related⟩, source.frame, realized⟩, ?_⟩
  cases step with
  | define instruction execution => cases site.instruction.symm.trans instruction
  | effect instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    let enteredFrame : GIR.Frame := { frame with scopes := (block.scope, state.nextScope) :: frame.scopes }
    let enteredState : St := { state with nextScope := state.nextScope + 1 }
    have enteredRun : execEff cx.fn frame (.enter block.scope) state = .ok enteredFrame enteredState := by
      simp [execEff, freshScope, bind_apply, pure_apply, enteredFrame, enteredState]
    have equal := Res.ok.inj (execution.symm.trans enteredRun)
    rcases equal with ⟨rfl, rfl⟩
    let le := lowerEnv cfg.mod env.vars results
    let entered := emitEffect (.enter block.scope) le before
    let scopedBuilder : LS := { entered.2 with stack := block.scope :: entered.2.stack }
    have emitted : emitEffect (.enter block.scope) le before = (entered.1, entered.2) := rfl
    obtain ⟨sameValues, sameStack, nextPoint, _⟩ :=
      emitEffect_facts emitted atPoint (generated_block_enter_extended extended)
    have scopedPoint : scopedBuilder.pp = some (point.1, point.2 + 1) := by
      simpa only [scopedBuilder, LS.pp] using nextPoint
    have scopedRelated : Rel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx enteredFrame scopedBuilder := by
      refine ⟨related.prof, related.slots, related.act, ?_, related.depth, ?_⟩
      · simp [enteredFrame, related.scopes]
      · simp [scopedBuilder, sameStack, related.stack]
    obtain ⟨cursor⟩ := source.parameterPrefix 0
    have framed : Core.Sound.Frame cfg.mod source.world cursor.typing
        { source.rootsEnv with scopes := block.scope :: source.rootsEnv.scopes }
        { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        enteredState source.context.inputFuture := by
      simpa only [List.take_zero, List.map_nil, List.nil_append, preStore, enteredState] using cursor.frame
    have carried := RetainedSsaMap.enter_scope source.frame source.fresh realized
    refine ⟨cursor, coverage, rfl, rfl, rfl, ?_, ⟨⟨scopedBuilder, scopedPoint, scopedRelated⟩, framed, ?_⟩⟩
    · change map.Bounded entered.2.vals.size
      rw [sameValues]
      exact bounded
    · simpa only [RetainedSsaMap.Realizes, enteredFrame, enteredState] using carried
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

end Goose.Lower
