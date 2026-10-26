import Goose.Lower.DemandGeneratedIndex

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_index_runtime_stop {cfg : Cfg} {env : Env} {view : View} {index : Expr}
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
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, indexedState⟩)
    (extended : ExtT (lowerPlace (.elem view index origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {targetFuel : Nat} {stop : Stop}
    (nonTimeout : stop ≠ .timeout)
    (stopped : DemandInstructionStop cx targetFuel ⟨point, frame, indexedState⟩ stop after) :

    ∃ child : ExprSource cfg env index viewedState, source.ExpressionChildAt child 1 rfl ∧ map.Covers required ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs ⟨point, frame, indexedState⟩ ∧
      stop = .abort .indexOob origin ∧ after = indexedState ∧
      evalPlace (fuel + 1) cfg env (.elem view index origin) state = .stop stop after := by
  let le := lowerEnv cfg.mod env.vars results
  let viewRun := lowerView view le before
  let indexRun := lowerExpr index le viewRun.2
  have site := GeneratedDemandInstruction.indexChecked_auto occurrence rows indexPost.pp extended
  have viewCell := (indexPost.same viewRun.1 (viewPost.lt (viewRun.1, .view sample) (by simp [viewRun, le]))).trans
    (viewPost.has (viewRun.1, .view sample) (by simp [viewRun, le]))
  have indexCell := indexPost.has (indexRun.1, .val value) (by simp [indexRun, viewRun, le])
  obtain ⟨type, _, _, _, _, nextChild⟩ := source.elemChildren origin
  obtain ⟨child, _, _, childType, canonical⟩ := nextChild fuel sample viewedState viewed
  have childResult := child.result fuel value indexed
  have childRealized : map.Realizes cfg.mod child.world env ⟨point, frame, indexedState⟩ := by
    simpa only [canonical.world] using realized
  refine ⟨child, canonical, coverage, ⟨⟨_, indexPost.pp, indexPost.rel⟩, childResult.frame, childRealized⟩, ?_⟩
  have integerTyped := childResult.typed
  rw [childType] at integerTyped
  obtain ⟨integer, valueEq⟩ := hasTy_int integerTyped
  subst value
  dsimp only [viewRun, indexRun, le] at viewCell indexCell
  cases stopped with
  | timeout => exact False.elim (nonTimeout rfl)
  | definition instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    simp only [execOp, execPure, getView_of viewCell, getVal_of indexCell, pure_bind, expectInt,
      bind_apply, pure_apply] at execution
    by_cases within : 0 ≤ integer ∧ integer < (sample.len : Int)
    · simp [within, pure_apply] at execution
    · simp [within, abortAtOrg, abortAt, M.stop] at execution
      rcases execution with ⟨rfl, rfl⟩
      refine ⟨rfl, rfl, ?_⟩
      simp [evalPlace, bind_apply, viewed, indexed, expectInt, pure_apply, within, abortAt, M.stop]
  | effect instruction execution => cases site.instruction.symm.trans instruction

end Goose.Lower
