import Goose.Lower.DemandGeneratedSnapshot
import Goose.Lower.DemandExpressionResult

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

private theorem load_reflection {cfg : Cfg} {env : Env} {place : Place} {sourceFuel targetFuel : Nat}
    {state addressedState after : St} {location : Loc} {value : RVal}
    (placed : evalPlace sourceFuel cfg env place state = .ok location addressedState)
    {cx : FnCtx} {frame : GIR.Frame} {address : ValueId}
    (cell : frame.vals[address]? = some (.val (.ref location)))
    (executed : execOp targetFuel cx frame (.load address) addressedState = .ok value after) :
    ∃ loaded, value = .val loaded ∧ after = addressedState ∧
      evalExpr (sourceFuel + 1) cfg env (.read place) state = .ok loaded after := by
  simp only [execOp, execPure, getVal_of cell, expectRef, bind_apply, pure_apply] at executed
  cases read : addressedState.store.read location with
  | error error => simp [readLoc, read] at executed
  | ok stored =>
    simp [readLoc, read] at executed
    rcases executed with ⟨rfl, rfl⟩
    refine ⟨stored, rfl, rfl, ?_⟩
    simp [evalExpr, bind_apply, placed, readLoc, read]

theorem accepted_generated_load_runtime_step_independent {cfg : Cfg} {env : Env} {place : Place}
    {state addressedState after : St} (source : ExprSource cfg env (.read place) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.read place)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {fuel : Nat} {location : Loc}
    (placed : evalPlace fuel cfg env place state = .ok location addressedState)
    {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx before initial
      (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (bounded : map.Bounded (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, addressedState⟩)
    (extended : ExtT (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame addressedState next nextFrame after) :
    ∃ child : PlaceSource cfg env place state, source.ReadChildAt child ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs ⟨point, frame, addressedState⟩ ∧
    ∃ value, next = (point.1, point.2 + 1) ∧
      nextFrame = frame.set (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).1 (.val value) ∧
      evalExpr (fuel + 1) cfg env (.read place) state = .ok value after ∧
      Post cfg env cx before initial (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).2
        nextFrame next [((lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).1, .val value)] ∧
      DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨next, nextFrame, after⟩ ∧
      ∀ aliases, source.rootsEnv.access.aliasExpr source.path (.read place) = .ok aliases →
        (map.addValues (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
          cfg.mod source.world env ⟨next, nextFrame, after⟩ := by
  have site := GeneratedDemandInstruction.load_auto occurrence rows post.pp extended
  have cell := post.has ((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location)) (by simp)
  obtain ⟨child, _, _, canonical⟩ := source.readChild
  have childResult := child.result fuel location placed
  have childRealized : map.Realizes cfg.mod child.world env ⟨point, frame, addressedState⟩ := by
    simpa only [canonical.world] using realized
  refine ⟨child, canonical, ⟨⟨_, post.pp, post.rel⟩, childResult.frame, childRealized⟩, ?_⟩
  cases step with
  | define instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    obtain ⟨value, rfl, stateEq, evaluated⟩ := load_reflection placed cell execution
    subst after
    let le := lowerEnv cfg.mod env.vars results
    let addressed := lowerPlace place le before
    let loaded := emitDef (.load addressed.1) le addressed.2
    let built := lowerExpr (.read place) le before
    have emitted : emitDef (.load addressed.1) le addressed.2 = (loaded.1, loaded.2) := rfl
    have extension := generated_read_load_extended extended
    obtain ⟨leafPost, _⟩ := Post.def_leaf (Post.init post.rel post.pp) emitted extension (.val value)
    obtain ⟨wholePost, _⟩ := Post.def_leaf post emitted extension (.val value)
    have recordRun : recordReadValueRootRecipe loaded.1 place le loaded.2 =
        ((), (recordReadValueRootRecipe loaded.1 place le loaded.2).2) := by
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · rfl
    have recordedPost := Post.recordReadValueRootRecipe wholePost recordRun
    have finalPost : Post cfg env cx before initial built.2 (frame.set built.1 (.val value))
        (point.1, point.2 + 1) [(built.1, .val value)] := by
      simpa only [built, lowerExpr_read_run] using recordedPost
    have result := source.result (fuel + 1) value evaluated
    have carried : map.Realizes cfg.mod source.world env
        ⟨(point.1, point.2 + 1), frame.set built.1 (.val value), addressedState⟩ := by
      simpa only [RetainedSsaMap.Realizes, built, lowerExpr_read_run] using
        realized.retained leafPost.same bounded.1 bounded.2 RetainsAliases.refl
    refine ⟨value, rfl, rfl, evaluated, finalPost,
      ⟨⟨_, finalPost.pp, finalPost.rel⟩, result.frame, carried⟩, ?_⟩
    intro aliases query
    exact RetainedSsaMap.addValues_realizes carried
      (fun alias member => result.generated_value finalPost query member)
  | effect instruction execution => cases site.instruction.symm.trans instruction
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction


theorem accepted_generated_load_runtime_step {cfg : Cfg} {env : Env} {place : Place}
    {state addressedState after : St} (source : ExprSource cfg env (.read place) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.read place)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) {fuel : Nat} {location : Loc}
    (placed : evalPlace fuel cfg env place state = .ok location addressedState)
    {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx before initial
      (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (bounded : map.Bounded (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, addressedState⟩)
    (extended : ExtT (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame addressedState next nextFrame after) :
    ∃ child : PlaceSource cfg env place state, source.ReadChildAt child ∧ map.Covers required ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs ⟨point, frame, addressedState⟩ ∧
    ∃ value, next = (point.1, point.2 + 1) ∧
      nextFrame = frame.set (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).1 (.val value) ∧
      evalExpr (fuel + 1) cfg env (.read place) state = .ok value after ∧
      Post cfg env cx before initial (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).2
        nextFrame next [((lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).1, .val value)] ∧
      DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨next, nextFrame, after⟩ ∧
      ∀ aliases, source.rootsEnv.access.aliasExpr source.path (.read place) = .ok aliases →
        (map.addValues (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
          cfg.mod source.world env ⟨next, nextFrame, after⟩ := by
  obtain ⟨child, canonical, demanded, value, pointEq, frameEq, evaluated, finalPost, finalDemand, added⟩ :=
    accepted_generated_load_runtime_step_independent source occurrence rows placed post bounded realized extended step
  exact ⟨child, canonical, coverage, demanded, value, pointEq, frameEq, evaluated, finalPost, finalDemand, added⟩

#print axioms accepted_generated_load_runtime_step_independent

end Goose.Lower
