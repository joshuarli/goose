import Goose.Lower.DemandGeneratedBody

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

private theorem block_leave_run {le : LEnv} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block} :
    (lowerBlock loop bindings want block le before).2 =
      let current := (lowerBlockValue want block.value le (demandBlockValueBefore le before loop bindings block)).2
      let released := (emitEffect (.leave block.scope) le current).2
      { released with stack := released.stack.drop 1 } := by
  cases block
  simp only [lowerBlock, inScope, bind_run, pushScope_run, popScope_run, pure_run,
    demandBlockValueBefore, demandBlockStatementsBefore, Core.Block.scope, Core.Block.stmts, Core.Block.value]

private theorem block_normal_prefix {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state addressedState valueState after : St} {fuel : Nat} {value : Val}
    (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } = .ok (.normal .unit) addressedState)
    (evaluated : valueFlow fuel cfg block.value
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } (.normal .unit) addressedState =
      .ok (.normal value) valueState)
    (released : Core.releaseScope env block.scope state.nextScope valueState = .ok () after) :
    execBlock (fuel + 1) cfg env pre block state = .ok (.normal value) after := by
  cases block with
  | mk scope stmts optional =>
    simp only [Core.Block.scope, Core.Block.stmts, Core.Block.value] at statements evaluated released
    cases optional with
    | none =>
      simp only [valueFlow, pure_apply, Res.ok.injEq, Flow.normal.injEq] at evaluated
      rcases evaluated with ⟨rfl, rfl⟩
      simp only [execBlock, bind_apply, freshScope, bindAll_eq, statements, pure_apply, released]
    | some expr =>
      change (evalExpr fuel cfg { env with scopes := (scope, state.nextScope) :: env.scopes } expr >>=
        fun result => pure (Flow.normal result)) addressedState = .ok (.normal value) valueState at evaluated
      cases expression : evalExpr fuel cfg { env with scopes := (scope, state.nextScope) :: env.scopes } expr addressedState with
      | stop stop final => simp [bind_apply, expression] at evaluated
      | ok result final =>
        simp only [bind_apply, expression, pure_apply, Res.ok.injEq, Flow.normal.injEq] at evaluated
        rcases evaluated with ⟨rfl, rfl⟩
        simp only [execBlock, bind_apply, freshScope, bindAll_eq, statements, expression, pure_apply, released]

theorem accepted_generated_block_leave_runtime_step {cfg : Cfg} {env : Env}
    {pre : List (VarId × Val)} {block : Core.Block} {state addressedState valueState after : St}
    (source : BlockSource cfg env pre block state) {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop bindings want block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial frame : GIR.Frame} {initialPoint point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨initialPoint, initial, state⟩)
    {fuel : Nat} {value : Val}
    (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } = .ok (.normal .unit) addressedState)
    (evaluated : valueFlow fuel cfg block.value
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } (.normal .unit) addressedState =
      .ok (.normal value) valueState)
    {cells : List (ValueId × RVal)}
    (post : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
      (lowerBlockValue want block.value (lowerEnv cfg.mod env.vars results)
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block)).2 frame point cells)
    (extended : ExtT (lowerBlock loop bindings want block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame valueState next nextFrame after) :
    GeneratedDemandInstruction cfg.mod source.rootsEnv.access cx.fn required
      (match block.value with
        | some _ => ⟨source.path ++ [block.stmts.length], .expression, .exit⟩
        | none => ⟨source.path, .block, .exit⟩) point (.eff (.leave block.scope)) ∧
      map.Covers required ∧
      next = (point.1, point.2 + 1) ∧ nextFrame = { frame with scopes := env.scopes } ∧
      execBlock (fuel + 1) cfg env pre block state = .ok (.normal value) after ∧
      Post cfg env cx before initial
        (lowerBlock loop bindings want block (lowerEnv cfg.mod env.vars results) before).2 nextFrame next cells ∧
      BlockResult source (.normal value) after ∧
      map.Bounded (lowerBlock loop bindings want block (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨next, nextFrame, after⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let current := (lowerBlockValue want block.value le (demandBlockValueBefore le before loop bindings block)).2
  let released := (emitEffect (.leave block.scope) le current).2
  have site := GeneratedDemandInstruction.blockLeave_auto occurrence rows post.pp extended
  refine ⟨site, coverage, ?_⟩
  cases step with
  | define instruction execution => cases site.instruction.symm.trans instruction
  | effect instruction execution =>
    cases site.instruction.symm.trans instruction
    have effect : execEff cx.fn frame (.leave block.scope) =
        Core.releaseScope env block.scope state.nextScope >>= fun _ =>
          pure ({ frame with scopes := env.scopes } : GIR.Frame) := by
      simp only [execEff, post.rel.scopes, ↓reduceIte]
      rw [releaseScope_eq post.rel]
      rfl
    rw [effect] at execution
    have releasedRun : Core.releaseScope env block.scope state.nextScope valueState = .ok ()
        { valueState with store := releaseVars env.vars env.act block.scope state.nextScope env.vars.size valueState.store } := rfl
    simp only [bind_apply, releasedRun, pure_apply, Res.ok.injEq] at execution
    rcases execution with ⟨rfl, rfl⟩
    have evaluatedBlock := block_normal_prefix statements evaluated releasedRun
    have emitted : emitEffect (.leave block.scope) le current = ((), released) := by
      have : (emitEffect (.leave block.scope) le current).1 = () := rfl
      exact Prod.ext this rfl
    obtain ⟨sameSize, sameStack, nextPoint, _⟩ :=
      emitEffect_facts emitted post.pp (generated_block_leave_extended extended)
    have finalEq := @block_leave_run le before loop bindings want block
    have finalRelated : Rel cfg env cx { frame with scopes := env.scopes }
        (lowerBlock loop bindings want block le before).2 := by
      refine ⟨post.rel.prof, post.rel.slots, post.rel.act, rfl, post.rel.depth, ?_⟩
      rw [finalEq]
      change released.stack.drop 1 = env.scopes.map Prod.fst
      rw [sameStack, post.rel.stack]
      rfl
    have finalPoint : (lowerBlock loop bindings want block le before).2.pp = some (point.1, point.2 + 1) := by
      rw [finalEq]
      exact nextPoint
    have finalSize : (lowerBlock loop bindings want block le before).2.vals.size = current.vals.size := by
      rw [finalEq]
      exact sameSize
    have finalPost : Post cfg env cx before initial (lowerBlock loop bindings want block le before).2
        { frame with scopes := env.scopes } (point.1, point.2 + 1) cells :=
      post.rescope rfl rfl finalPoint finalSize rfl finalRelated
    have result := source.result (fuel + 1) (.normal value) evaluatedBlock
    have retained : RetainsAliases cfg.mod source.world env state.store (releaseVars env.vars env.act block.scope state.nextScope env.vars.size valueState.store)
        (map.values.map Prod.snd ++ map.runs.map Prod.snd) := by
      cases profile : cfg.mod.profile with
      | pilot => exact retainedAliases_of_storeLe (result.pilotStore profile) _
      | shrink => exact result.aliases.subset (admitted profile)
    have carried := realized.retained finalPost.same bounded.1 bounded.2 retained
    exact ⟨rfl, rfl, evaluatedBlock, finalPost, result, bounded.mono finalPost.mono,
      ⟨⟨_, finalPoint, finalRelated⟩, result.frame, carried⟩⟩
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

end Goose.Lower
