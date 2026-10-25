import Goose.Lower.FuelBoundTyped
import Goose.Lower.ReflectionEffects

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem TypedBlockFuelBound.function {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {pre : List (SlotId × ValueId × OriginId)} {pre' : List (VarId × Val)}
    {want : Bool} {block : Core.Block}
    (reflection : TypedBlockFuelBound sourceFuel fuel cfg results none pre pre' want block)
    (env : Env) (state : St) (source : BlockSource cfg env pre' block state)
    (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (loops : source.typingEnv.loops = 0)
    (ls after : LS) (result : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame)
    (lowering : lowerBlock none pre want block (lowerEnv cfg.mod env.vars results) ls = (result,after))
    (point : ls.pp = some pt) (extension : ExtT after cx.fn.blocks) (rel : Rel cfg env cx fr ls)
    (prerel : PreRel fr pre pre') (moduleEq : cx.cfg.mod = lower cfg.mod)
    (resultsEq : cx.fn.results = results) (generated : GeneratedBuilderState ls) :
    FuelBoundAt sourceFuel fuel cx pt fr (fun n => execBlock n cfg env pre' block >>= prepareReturn env)
      (fun flow _ pt' fr' => BlockFlowPost cfg env cx ls fr after block want result flow pt' fr') state := by
  have align : LoopSourceMatches source.typingEnv none := ⟨fun _ => loops,fun _ => rfl⟩
  have whole := reflection env state source metadata align ls after result pt cx fr lowering point
    extension rel prerel moduleEq resultsEq trivial trivial trivial generated trivial
  simp only [prepareLoopFlow_none] at whole
  exact whole.mono (fun flow after pt' fr' post => BlockLoopPost.none.mp post)


theorem FuelBoundAt.complete_expectReturned {cx : FnCtx} {pt : Pt} {fr : Frame}
    {source : Nat → M Flow} {post : Flow → St → Pt → Frame → Prop} {state : St} {sourceFuel fuel : Nat}
    (reflection : FuelBoundAt sourceFuel fuel cx pt fr source post state)
    (terminal : ∀ n flow after pt' fr', source n state = .ok flow after → post flow after pt' fr' →
      ∃ value, (flow = .normal value ∨ flow = .ret value) ∧ ReturnEndpoint cx pt' fr' value) :
    FuelBoundM sourceFuel fuel (fun n => source n >>= expectReturned) (fun n => runAt cx pt fr n) state := by
  intro result nonTimeout run
  rcases reflection result nonTimeout run with success | stopped
  · obtain ⟨flow, after, pt', fr', residual, sourceRun, matched, bound, continuation⟩ := success
    obtain ⟨value, sourceFlow, returnEndpoint⟩ := terminal sourceFuel flow after pt' fr' sourceRun matched
    have coreResult : expectReturned flow after = .ok value after := by
      rcases sourceFlow with sourceNormal | sourceReturn
      · rw [sourceNormal]
        rfl
      · rw [sourceReturn]
        rfl
    have targetResult : result = .ok value after := by
      cases residual with
      | zero =>
          have timeoutResult : result = .stop .timeout after := by
            calc
              result = runAt cx pt' fr' 0 after := continuation.symm
              _ = .stop .timeout after := rfl
          exact (nonTimeout after timeoutResult).elim
      | succ extra =>
          calc
            result = runAt cx pt' fr' (extra + 1) after := continuation.symm
            _ = .ok value after := returnEndpoint.run after extra
    change (source sourceFuel >>= expectReturned) state = result
    have sourceResult : (source sourceFuel >>= expectReturned) state = .ok value after := by
      rw [bind_apply, sourceRun]
      exact coreResult
    exact sourceResult.trans targetResult.symm
  · obtain ⟨stop, after, sourceRun, targetRun⟩ := stopped
    change (source sourceFuel >>= expectReturned) state = result
    calc
      (source sourceFuel >>= expectReturned) state = .stop stop after := by rw [bind_apply, sourceRun]
      _ = result := targetRun.symm


theorem FuelBoundAt.complete_value {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {source : Nat → M Val} {post : Val → St → Pt → GIR.Frame → Prop} {state : St} {sourceFuel fuel : Nat}
    (reflection : FuelBoundAt sourceFuel fuel cx pt fr source post state)
    (terminal : ∀ value after pt' fr', post value after pt' fr' → ReturnEndpoint cx pt' fr' value) :
    FuelBoundM sourceFuel fuel source (fun n => runAt cx pt fr n) state := by
  intro result nonTimeout run
  rcases reflection result nonTimeout run with success | stopped
  · obtain ⟨value,after,pt',fr',residual,sourceRun,matched,bound,continuation⟩ := success
    have endpoint := terminal value after pt' fr' matched
    cases residual with
    | zero => exact (nonTimeout after (continuation.symm.trans rfl)).elim
    | succ extra =>
      have returned := endpoint.run after extra
      exact sourceRun.trans (continuation.symm.trans returned).symm
  · obtain ⟨stop,after,sourceRun,targetRun⟩ := stopped
    exact sourceRun.trans targetRun.symm

end Goose.Lower
