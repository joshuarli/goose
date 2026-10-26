import Goose.Lower.DemandGeneratedLoad

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

structure GeneratedLengthSite (module : Core.Module) (access : AccessEnv) (function : Func)
    (le : LEnv) (root : DemandNode) (path : List Nat) (view : View) (before : LS)
    (required : RetainedSsaMap) (point : Pt) : Prop where
  occurrence : GeneratedDemandOccurrence module function le root path (.expression (.len view)) before
  rows : GeneratedDemandRows module access (.first occurrence (.expressionView rfl)) required
  atPoint : (lowerView view le before).2.pp = some point
  extended : ExtT (lowerExpr (.len view) le before).2 function.blocks

theorem lowerExpr_len_run (view : View) (le : LEnv) (before : LS) :
    lowerExpr (.len view) le before =
      emitDef (.viewLen (lowerView view le before).1) le (lowerView view le before).2 := by
  simp only [lowerExpr, bind_run]

def GeneratedLengthSite.label (path : List Nat) : DemandSourceLabel := ⟨path ++ [0], .view, .exit⟩

theorem GeneratedLengthSite.instruction {module : Core.Module} {access : AccessEnv} {function : Func}
    {le : LEnv} {root : DemandNode} {path : List Nat} {view : View} {before : LS}
    {required : RetainedSsaMap} {point : Pt}
    (site : GeneratedLengthSite module access function le root path view before required point) :
    instAt function point = some (.def (lowerExpr (.len view) le before).1
      (.viewLen (lowerView view le before).1)) := by
  have emitted : emitDef (.viewLen (lowerView view le before).1) le (lowerView view le before).2 =
      ((lowerExpr (.len view) le before).1, (lowerExpr (.len view) le before).2) := by
    rw [lowerExpr_len_run]
  simpa only [instAt_eq] using (emitDef_facts emitted site.atPoint site.extended).2.2.2.2

theorem accepted_generated_length_runtime_step {cfg : Cfg} {env : Env} {view : View}
    {state sampledState after : St} (source : ExprSource cfg env (.len view) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    {required map : RetainedSsaMap} {point : Pt}
    (site : GeneratedLengthSite cfg.mod source.rootsEnv.access cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path view before required point)
    (coverage : map.Covers required) {fuel : Nat} {sample : ViewVal}
    (sampled : evalView fuel cfg env view state = .ok sample sampledState)
    {initial frame : GIR.Frame}
    (post : Post cfg env cx before initial
      (lowerView view (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerView view (lowerEnv cfg.mod env.vars results) before).1, .view sample)])
    (bounded : map.Bounded (lowerView view (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, sampledState⟩)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame sampledState next nextFrame after) :
    ∃ child : ViewSource cfg env view state, source.ViewChildAt child 0 rfl ∧ map.Covers required ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs ⟨point, frame, sampledState⟩ ∧
      after = sampledState ∧ next = (point.1, point.2 + 1) ∧
      nextFrame = frame.set (lowerExpr (.len view) (lowerEnv cfg.mod env.vars results) before).1
        (.val (.int .i64 sample.len)) ∧
      evalExpr (fuel + 1) cfg env (.len view) state = .ok (.int .i64 sample.len) after ∧
      Post cfg env cx before initial (lowerExpr (.len view) (lowerEnv cfg.mod env.vars results) before).2
        nextFrame next [((lowerExpr (.len view) (lowerEnv cfg.mod env.vars results) before).1,
          .val (.int .i64 sample.len))] ∧
      DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨next, nextFrame, after⟩ := by
  obtain ⟨child, typing, roots, canonical, future⟩ := source.lenChild
  have childResult := child.result fuel sample sampled
  have childRealized : map.Realizes cfg.mod child.world env ⟨point, frame, sampledState⟩ := by
    simpa only [canonical.world] using realized
  refine ⟨child, canonical, coverage, ⟨⟨_, post.pp, post.rel⟩, childResult.frame, childRealized⟩, ?_⟩
  have cell := post.has ((lowerView view (lowerEnv cfg.mod env.vars results) before).1, .view sample) (by simp)
  cases step with
  | define instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    simp only [execOp, execPure, getView_of cell, bind_apply, pure_apply] at execution
    rcases execution with ⟨rfl, rfl⟩
    have evaluated : evalExpr (fuel + 1) cfg env (.len view) state =
        .ok (.int .i64 sample.len) sampledState := by
      simp only [evalExpr, bind_apply, sampled, pure_apply]
    have emitted : emitDef (.viewLen (lowerView view (lowerEnv cfg.mod env.vars results) before).1)
        (lowerEnv cfg.mod env.vars results) (lowerView view (lowerEnv cfg.mod env.vars results) before).2 =
        (lowerExpr (.len view) (lowerEnv cfg.mod env.vars results) before) := by
      rw [lowerExpr_len_run]
    obtain ⟨leafPost, _⟩ := Post.def_leaf (Post.init post.rel post.pp) emitted site.extended
      (.val (.int .i64 sample.len))
    obtain ⟨wholePost, _⟩ := Post.def_leaf post emitted site.extended (.val (.int .i64 sample.len))
    have result := source.result (fuel + 1) (.int .i64 sample.len) evaluated
    have carried := realized.retained leafPost.same bounded.1 bounded.2 RetainsAliases.refl
    exact ⟨rfl, rfl, rfl, evaluated, wholePost,
      ⟨⟨_, wholePost.pp, wholePost.rel⟩, result.frame, carried⟩⟩
  | effect instruction execution => cases site.instruction.symm.trans instruction
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

#print axioms accepted_generated_length_runtime_step
end Goose.Lower
