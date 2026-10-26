import Goose.Lower.DemandGeneratedBody

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

private theorem clear_reflection {cfg : Cfg} {env : Env} {place : Place} {origin : OriginId} {fuel : Nat}
    {state addressedState after : St} {location : Loc} {cx : FnCtx} {frame nextFrame : GIR.Frame} {address : ValueId}
    (placed : evalPlace fuel cfg env place state = .ok location addressedState)
    (cell : frame.vals[address]? = some (.val (.ref location)))
    (executed : execEff cx.fn frame (.clear address (some origin)) addressedState = .ok nextFrame after) :
    nextFrame = frame ∧ execStmt (fuel + 1) cfg env (.clear place origin) state = .ok (.normal .unit) after := by
  simp only [execEff, getVal_of cell, expectRef, bind_apply, pure_apply] at executed
  cases truncated : truncateLoc location 0 addressedState with
  | stop stop final => simp [truncated] at executed
  | ok result final =>
    cases result
    simp only [truncated, Res.ok.injEq] at executed
    rcases executed with ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    simp only [execStmt, bind_apply, placed]
    change (truncateLoc location 0 >>= fun _ => pure (Flow.normal Val.unit)) addressedState = _
    simp only [bind_apply, truncated, pure_apply]

theorem accepted_generated_clear_runtime_step {cfg : Cfg} {env : Env} {place : Place} {origin : OriginId}
    {state addressedState after : St} (source : StmtSource cfg env (.clear place origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.clear place origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial frame : GIR.Frame} {initialPoint point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨initialPoint, initial, state⟩)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location addressedState)
    (post : Post cfg env cx before initial
      (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (extended : ExtT (lowerStmt loop (.clear place origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame addressedState next nextFrame after) :
    ∃ child : PlaceSource cfg env place state, source.PlaceChildAt child rfl ∧
      PlaceResult child location addressedState ∧ map.Covers required ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs ⟨point, frame, addressedState⟩ ∧
      next = (point.1, point.2 + 1) ∧ nextFrame = frame ∧
      execStmt (fuel + 1) cfg env (.clear place origin) state = .ok (.normal .unit) after ∧
      Post cfg env cx before initial
        (lowerStmt loop (.clear place origin) (lowerEnv cfg.mod env.vars results) before).2 nextFrame next [] ∧
      StmtResult source (.normal .unit) after ∧
      map.Bounded (lowerStmt loop (.clear place origin) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      DemandFrameAt cfg env cx source.world source.typingAfter source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨next, nextFrame, after⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace place le before
  let built := lowerStmt loop (.clear place origin) le before
  have site := GeneratedDemandInstruction.clear_auto occurrence rows post.pp extended
  have cell := post.has (addressed.1, .val (.ref location)) (by simp [addressed, le])
  obtain ⟨child, _, _, _, _, _, _, _, canonical⟩ := source.clearChild
  have childResult := child.result fuel location placed
  have beforeRetains : RetainsAliases cfg.mod source.world env state.store addressedState.store
      (map.values.map Prod.snd ++ map.runs.map Prod.snd) := by
    cases profile : cfg.mod.profile with
    | pilot =>
      have growth := childResult.pilotStore profile
      exact retainedAliases_of_storeLe growth _
    | shrink =>
      simpa only [canonical.world] using childResult.aliases.subset
        (fun alias member => canonical.retained alias (admitted profile alias member))
  have beforeCarried := realized.retained post.same bounded.1 bounded.2 beforeRetains
  have childCarried : map.Realizes cfg.mod child.world env ⟨point, frame, addressedState⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using beforeCarried
  refine ⟨child, canonical, childResult, coverage, ⟨⟨_, post.pp, post.rel⟩, childResult.frame, childCarried⟩, ?_⟩
  cases step with
  | define instruction execution => cases site.instruction.symm.trans instruction
  | effect instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    obtain ⟨rfl, evaluated⟩ := clear_reflection placed cell execution
    have emitted : emitEffect (.clear addressed.1 (some origin)) le addressed.2 = ((), built.2) := by
      simp only [built, addressed, lowerStmt, bind_run]
    obtain ⟨finalPost, _⟩ := Post.eff_leaf post emitted extended
    have result := source.result (fuel + 1) (.normal .unit) evaluated
    have retained : RetainsAliases cfg.mod source.world env state.store after.store
        (map.values.map Prod.snd ++ map.runs.map Prod.snd) := by
      cases profile : cfg.mod.profile with
      | pilot => exact retainedAliases_of_storeLe (result.pilotStore profile) _
      | shrink => exact result.aliases.subset (admitted profile)
    have carried := realized.retained finalPost.same bounded.1 bounded.2 retained
    exact ⟨rfl, rfl, evaluated, finalPost, result, bounded.mono finalPost.mono,
      ⟨⟨_, finalPost.pp, finalPost.rel⟩, result.frame, carried⟩⟩
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

end Goose.Lower
