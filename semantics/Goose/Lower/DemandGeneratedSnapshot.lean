import Goose.Lower.DemandGeneratedPlaceLeaves
import Goose.Evidence.Execution

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

private theorem snapshot_execution {cfg : Cfg} {env : Env} {place : Place} {fuel : Nat}
    {state sampledState after : St} {location : Loc} {sample : ViewVal}
    (placed : evalPlace fuel cfg env place state = .ok location sampledState)
    (sampled : evalView (fuel + 1) cfg env (.of place) state = .ok sample after)
    {cx : FnCtx} {frame : GIR.Frame} {address : ValueId}
    (cell : frame.vals[address]? = some (.val (.ref location))) (kind : SnapshotMode) :
    after = sampledState ∧ ∀ targetFuel, execOp targetFuel cx frame (.snapshot kind address) sampledState =
      .ok (.view sample) sampledState := by
  simp only [evalView, bind_apply, placed] at sampled
  cases read : sampledState.store.read location with
  | error error => simp [readLoc, read] at sampled
  | ok value =>
    cases value <;> simp [readLoc, read, expectArray, fault, M.stop, pure_apply] at sampled
    all_goals rcases sampled with ⟨rfl, rfl⟩
    all_goals refine ⟨rfl, fun targetFuel => ?_⟩
    all_goals simp [execOp, execPure, getVal_of cell, expectRef, readLoc, read, expectArray,
      bind_apply, pure_apply]

private theorem snapshot_reflection {cfg : Cfg} {env : Env} {place : Place} {sourceFuel targetFuel : Nat}
    {state sampledState after : St} {location : Loc} {value : RVal}
    (placed : evalPlace sourceFuel cfg env place state = .ok location sampledState)
    {cx : FnCtx} {frame : GIR.Frame} {address : ValueId}
    (cell : frame.vals[address]? = some (.val (.ref location))) {mode : SnapshotMode}
    (executed : execOp targetFuel cx frame (.snapshot mode address) sampledState = .ok value after) :
    ∃ sample, value = .view sample ∧ evalView (sourceFuel + 1) cfg env (.of place) state = .ok sample after := by
  simp only [execOp, execPure, getVal_of cell, expectRef, bind_apply, pure_apply] at executed
  cases read : sampledState.store.read location with
  | error error => simp [readLoc, read] at executed
  | ok stored =>
    cases stored <;> simp [readLoc, read, expectArray, fault, M.stop, pure_apply] at executed
    all_goals rcases executed with ⟨rfl, rfl⟩
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [evalView, bind_apply, placed, readLoc, read, expectArray, pure_apply]

theorem accepted_generated_snapshot_step {cfg : Cfg} {env : Env} {place : Place}
    {state sampledState after : St} (source : ViewSource cfg env (.of place) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.view (.of place)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) {fuel : Nat} {location : Loc} {sample : ViewVal}
    (placed : evalPlace fuel cfg env place state = .ok location sampledState)
    (sampled : evalView (fuel + 1) cfg env (.of place) state = .ok sample after)
    {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx before initial
      (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (bounded : map.Bounded (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, sampledState⟩)
    (extended : ExtT (lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    after = sampledState ∧
    GeneratedDemandInstruction cfg.mod source.rootsEnv.access cx.fn required ⟨source.path, .view, .exit⟩ point
      (.def (lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).1
        (.snapshot (match (generalizing := false) place with | .var _ | .global _ => .owner | _ => .borrowed)
          (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1)) ∧
    DemandUniformTraversal cx (fun runtime => map.Covers required ∧
      DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
        map.values map.runs runtime) 1 ⟨point, frame, sampledState⟩
      ⟨(point.1, point.2 + 1), frame.set
        (lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).1 (.view sample), after⟩ ∧
    Post cfg env cx before initial
      (lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).2
      (frame.set (lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).1 (.view sample))
      (point.1, point.2 + 1)
      [((lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).1, .view sample)] ∧
    ∀ aliases, source.rootsEnv.access.aliasView source.path (.of place) = .ok aliases →
      (map.addRuns (lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
        cfg.mod source.world env ⟨(point.1, point.2 + 1),
          frame.set (lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).1 (.view sample), after⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace place le before
  let kind := match (generalizing := false) place with | .var _ | .global _ => SnapshotMode.owner | _ => .borrowed
  let built := lowerView (.of place) le before
  have emitted : emitDef (.snapshot kind addressed.1) le addressed.2 = (built.1, built.2) := by
    cases place <;> simp only [kind, addressed, built, lowerView, bind_run]
  have cell := post.has (addressed.1, .val (.ref location)) (by simp [addressed, le])
  obtain ⟨stateEq, operation⟩ := snapshot_execution placed sampled cell kind
  subst after
  obtain ⟨child, typing, roots, canonical⟩ := source.ofChild
  have childResult := child.result fuel location placed
  have result := source.result (fuel + 1) sample sampled
  obtain ⟨leafPost, instruction⟩ := Post.def_leaf (Post.init post.rel post.pp) emitted extended (.view sample)
  obtain ⟨wholePost, _⟩ := Post.def_leaf post emitted extended (.view sample)
  have carried := realized.retained leafPost.same bounded.1 bounded.2 RetainsAliases.refl
  have beforeFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
      sampledState source.context.outputFuture := by
    rw [← canonical.world, ← typing, ← roots, ← canonical.outputFuture]
    exact childResult.frame
  refine ⟨rfl, .snapshot_auto occurrence rows post.pp extended,
    .next ⟨coverage, ⟨⟨_, post.pp, post.rel⟩, beforeFrame, realized⟩⟩
      (fun targetFuel => .definition instruction (operation targetFuel))
      (.done ⟨coverage, ⟨⟨_, wholePost.pp, wholePost.rel⟩, result.frame, carried⟩⟩), wholePost, ?_⟩
  intro aliases query
  exact result.extend_generated_runs query carried (wholePost.has (built.1, .view sample) (by simp))

theorem accepted_generated_snapshot_runtime_step {cfg : Cfg} {env : Env} {place : Place}
    {state sampledState after : St} (source : ViewSource cfg env (.of place) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.view (.of place)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) {fuel : Nat} {location : Loc}
    (placed : evalPlace fuel cfg env place state = .ok location sampledState)
    {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx before initial
      (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (bounded : map.Bounded (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, sampledState⟩)
    (extended : ExtT (lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame sampledState next nextFrame after) :

    ∃ sample, next = (point.1, point.2 + 1) ∧
      nextFrame = frame.set (lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).1 (.view sample) ∧
      evalView (fuel + 1) cfg env (.of place) state = .ok sample after ∧
      Post cfg env cx before initial (lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).2
        nextFrame next [((lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).1, .view sample)] ∧
      DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨next, nextFrame, after⟩ ∧
      ∀ aliases, source.rootsEnv.access.aliasView source.path (.of place) = .ok aliases →
        (map.addRuns (lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
          cfg.mod source.world env ⟨next, nextFrame, after⟩ := by
  have site := GeneratedDemandInstruction.snapshot_auto occurrence rows post.pp extended
  have cell := post.has ((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location)) (by simp)
  cases step with
  | define instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    obtain ⟨sample, rfl, sampled⟩ := snapshot_reflection placed cell execution
    obtain ⟨stateEq, generated, traversal, finalPost, produced⟩ :=
      accepted_generated_snapshot_step source occurrence rows coverage placed sampled post bounded realized extended
    exact ⟨sample, rfl, rfl, sampled, finalPost, traversal.last_valid.2, produced⟩
  | effect instruction execution => cases site.instruction.symm.trans instruction
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

end Goose.Lower
