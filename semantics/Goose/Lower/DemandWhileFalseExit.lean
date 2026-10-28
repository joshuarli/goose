import Goose.Lower.DemandWhileExitBuilder

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_false_exit {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state after : St} (source : StmtSource cfg env (.while condition body origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {fuel : Nat} (evaluated : evalExpr fuel cfg env condition state = .ok (.bool false) after)
    {cx : FnCtx} {results : List Ty} {header : BlockId} {before built : LS}
    {initial frame : GIR.Frame} {point : Pt} {map : RetainedSsaMap}
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool false) after point frame)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) before = ((), built)) (extended : ExtT built cx.fn.blocks) :
    ∃ exitBlock,
      (∀ targetFuel, DemandInstructionStep cx targetFuel ⟨point, frame, after⟩ ⟨(exitBlock, 0), frame, after⟩) ∧
      execStmt (fuel + 2) cfg env (.while condition body origin) state = .ok (.normal .unit) after ∧
      Post cfg env cx before initial built frame (exitBlock, 0) [] ∧ map.Bounded built.vals.size ∧
      map.Realizes cfg.mod source.world env ⟨(exitBlock, 0), frame, after⟩ := by
  obtain ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, value, forkRun, bodyEq, bodyRun,
    jumpRun, finalEq, forkExtended, bodyExtended, jumpExtended, exitPoint, exitStack, exitVals⟩ :=
    generated_while_exit_builder lowered boundary.post.pp extended
  have cell := boundary.post.has ((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool false)) (by simp)
  have step : ∀ targetFuel, DemandInstructionStep cx targetFuel ⟨point, frame, after⟩ ⟨(exitBlock, 0), frame, after⟩ := by
    intro targetFuel
    simpa using generated_if_branch_step false forkRun boundary.post.pp forkExtended cell targetFuel
  have done : execStmt (fuel + 2) cfg env (.while condition body origin) state = .ok (.normal .unit) after := by
    simpa only [execStmt] using (while_condition_false (body := body) evaluated)
  have post := generated_if_skip_post boundary.post exitPoint exitStack exitVals
  have bounded := boundary.bounded.mono exitVals
  have realized : map.Realizes cfg.mod source.world env ⟨(exitBlock, 0), frame, after⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using boundary.demanded.operands
  exact ⟨exitBlock, step, done, post, bounded, realized⟩

#print axioms accepted_generated_while_false_exit
end Goose.Lower
