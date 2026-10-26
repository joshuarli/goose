import Goose.Lower.DemandGeneratedLoad

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

private theorem index_reflection {cfg : Cfg} {env : Env} {view : View} {index : Expr} {origin : OriginId}
    {sourceFuel targetFuel : Nat} {state viewedState indexedState after : St} {sample : ViewVal}
    {indexValue : Val} {value : RVal}
    (viewed : evalView sourceFuel cfg env view state = .ok sample viewedState)
    (indexed : evalExpr sourceFuel cfg env index viewedState = .ok indexValue indexedState)
    {cx : FnCtx} {frame : GIR.Frame} {viewId indexId : ValueId}
    (viewCell : frame.vals[viewId]? = some (.view sample))
    (indexCell : frame.vals[indexId]? = some (.val indexValue))
    (executed : execOp targetFuel cx frame (.indexChecked viewId indexId (some origin)) indexedState = .ok value after) :
    ∃ location, value = .val (.ref location) ∧ after = indexedState ∧
      evalPlace (sourceFuel + 1) cfg env (.elem view index origin) state = .ok location after := by
  cases indexValue <;>
    simp only [execOp, execPure, getView_of viewCell, getVal_of indexCell, pure_bind, expectInt,
      bind_apply, pure_apply, fault, M.stop, reduceCtorEq] at executed
  rename_i type integer
  by_cases bounded : 0 ≤ integer ∧ integer < (sample.len : Int)
  · simp only [bounded] at executed
    rcases executed with ⟨rfl, rfl⟩
    refine ⟨_, rfl, rfl, ?_⟩
    simp [evalPlace, bind_apply, viewed, indexed, expectInt, bounded, pure_apply]
  · simp [bounded, abortAtOrg, abortAt, M.stop] at executed

theorem accepted_generated_index_runtime_step {cfg : Cfg} {env : Env} {view : View} {index : Expr}
    {origin : OriginId} {state viewedState indexedState after : St}
    (source : PlaceSource cfg env (.elem view index origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.elem view index origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access (.index occurrence) required)
    (coverage : map.Covers required) {fuel : Nat} {sample : ViewVal} {value : Val}
    (viewed : evalView fuel cfg env view state = .ok sample viewedState)
    (indexed : evalExpr fuel cfg env index viewedState = .ok value indexedState)
    {initial viewFrame frame : GIR.Frame} {viewPoint point : Pt}
    (viewPost : Post cfg env cx before initial
      (lowerView view (lowerEnv cfg.mod env.vars results) before).2 viewFrame viewPoint
      [((lowerView view (lowerEnv cfg.mod env.vars results) before).1, .view sample)])
    (indexPost : Post cfg env cx (lowerView view (lowerEnv cfg.mod env.vars results) before).2 viewFrame
      (lowerExpr index (lowerEnv cfg.mod env.vars results)
        (lowerView view (lowerEnv cfg.mod env.vars results) before).2).2 frame point
      [((lowerExpr index (lowerEnv cfg.mod env.vars results)
        (lowerView view (lowerEnv cfg.mod env.vars results) before).2).1, .val value)])
    (bounded : map.Bounded (lowerExpr index (lowerEnv cfg.mod env.vars results)
      (lowerView view (lowerEnv cfg.mod env.vars results) before).2).2.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, indexedState⟩)
    (extended : ExtT (lowerPlace (.elem view index origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame indexedState next nextFrame after) :
    ∃ child : ExprSource cfg env index viewedState, source.ExpressionChildAt child 1 rfl ∧ map.Covers required ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs ⟨point, frame, indexedState⟩ ∧
    ∃ location, next = (point.1, point.2 + 1) ∧
      nextFrame = frame.set (lowerPlace (.elem view index origin) (lowerEnv cfg.mod env.vars results) before).1 (.val (.ref location)) ∧
      evalPlace (fuel + 1) cfg env (.elem view index origin) state = .ok location after ∧
      Post cfg env cx before initial (lowerPlace (.elem view index origin) (lowerEnv cfg.mod env.vars results) before).2
        nextFrame next [((lowerPlace (.elem view index origin) (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))] ∧
      PlaceResult source location after ∧
      DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨next, nextFrame, after⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let viewRun := lowerView view le before
  let indexRun := lowerExpr index le viewRun.2
  let built := lowerPlace (.elem view index origin) le before
  have site := GeneratedDemandInstruction.indexChecked_auto occurrence rows indexPost.pp extended
  have viewCell := (indexPost.same viewRun.1 (viewPost.lt (viewRun.1, .view sample) (by simp [viewRun, le]))).trans
    (viewPost.has (viewRun.1, .view sample) (by simp [viewRun, le]))
  have indexCell := indexPost.has (indexRun.1, .val value) (by simp [indexRun, viewRun, le])
  obtain ⟨_, _, _, _, _, nextChild⟩ := source.elemChildren origin
  obtain ⟨child, _, _, _, canonical⟩ := nextChild fuel sample viewedState viewed
  have childResult := child.result fuel value indexed
  have childRealized : map.Realizes cfg.mod child.world env ⟨point, frame, indexedState⟩ := by
    simpa only [canonical.world] using realized
  refine ⟨child, canonical, coverage, ⟨⟨_, indexPost.pp, indexPost.rel⟩, childResult.frame, childRealized⟩, ?_⟩
  cases step with
  | define instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    obtain ⟨location, rfl, stateEq, evaluated⟩ := index_reflection viewed indexed viewCell indexCell execution
    subst after
    have emitted : emitDef (.indexChecked viewRun.1 indexRun.1 (some origin)) le indexRun.2 = (built.1, built.2) := by
      simp only [viewRun, indexRun, built, lowerPlace, bind_run]
    obtain ⟨leafPost, _⟩ := Post.def_leaf (Post.init indexPost.rel indexPost.pp) emitted extended (.val (.ref location))
    obtain ⟨wholePost, _⟩ := Post.def_leaf (viewPost.comp indexPost) emitted extended (.val (.ref location))
    have result := source.result (fuel + 1) location evaluated
    have carried := realized.retained leafPost.same bounded.1 bounded.2 RetainsAliases.refl
    exact ⟨location, rfl, rfl, evaluated, wholePost, result,
      ⟨⟨_, wholePost.pp, wholePost.rel⟩, result.frame, carried⟩⟩
  | effect instruction execution => cases site.instruction.symm.trans instruction
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

end Goose.Lower
