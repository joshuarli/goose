import Goose.Lower.DemandIfJoinBuilder

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_if_skip {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {origin : OriginId} {state after : St} (source : StmtSource cfg env (.ifS condition yes none origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {sourceFuel : Nat} (evaluated : evalExpr sourceFuel cfg env condition state = .ok (.bool false) after)
    {cx : FnCtx} {results : List Ty} {before built : LS} {loop : Option LoopCtx}
    {initial frame : GIR.Frame} {point : Pt} {map : RetainedSsaMap}
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool false) after point frame)
    (lowered : lowerStmt loop (.ifS condition yes none origin) (lowerEnv cfg.mod env.vars results) before = ((), built))
    (extended : ExtT built cx.fn.blocks) :
    ∃ joinBlock, (∀ targetFuel, DemandInstructionStep cx targetFuel ⟨point, frame, after⟩ ⟨(joinBlock, 0), frame, after⟩) ∧
      execStmt (sourceFuel + 1) cfg env (.ifS condition yes none origin) state = .ok (.normal .unit) after ∧
      GeneratedStatementPrefixEnd source map cx before initial built loop (.normal .unit) ⟨(joinBlock, 0), frame, after⟩ := by
  obtain ⟨yesBlock, joinBlock, forked, branchStart, branchEnd, jumped, value, forkRun, startEq,
    branchRun, jumpRun, finalEq, forkExtended, branchExtended, jumpExtended, joinPoint, joinStack, joinVals⟩ :=
    generated_if_none_join_builder lowered boundary.post.pp extended
  have cell := boundary.post.has ((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool false)) (by simp)
  have step : ∀ targetFuel, DemandInstructionStep cx targetFuel ⟨point, frame, after⟩ ⟨(joinBlock, 0), frame, after⟩ := by
    intro targetFuel
    simpa using generated_if_branch_step false forkRun boundary.post.pp forkExtended cell targetFuel
  have sourceDone := if_false_source_skip (yes := yes) (origin := origin) evaluated
  have post := generated_if_skip_post boundary.post joinPoint joinStack joinVals
  have bounded := boundary.bounded.mono joinVals
  have realized : map.Realizes cfg.mod source.world env ⟨(joinBlock, 0), frame, after⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using boundary.demanded.operands
  exact ⟨joinBlock, step, sourceDone, .normal post (source.result _ _ sourceDone) bounded realized⟩

theorem accepted_generated_if_then_join {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {origin : OriginId} {state middle after : St} (source : StmtSource cfg env (.ifS condition yes none origin) state)
    (branch : BlockSource cfg env [] yes middle)
    (canonical : source.BlockChildAt branch 1 (by simp [DemandNode.child?, DemandNode.children]))
    {conditionFuel branchFuel : Nat}
    (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) middle)
    (branchDone : execBlock branchFuel cfg env [] yes middle = .ok (.normal .unit) after)
    {cx : FnCtx} {results : List Ty} {before conditionEnd forked branchStart branchEnd jumped built : LS}
    {loop : Option LoopCtx} {initial conditionFrame finalFrame : GIR.Frame} {conditionPoint branchPoint : Pt}
    {map required : RetainedSsaMap} {conditionId yesBlock joinBlock value : Nat}
    (conditionPost : Post cfg env cx before initial conditionEnd conditionFrame conditionPoint [(conditionId, .val (.bool true))])
    (forkRun : fork conditionId (lowerEnv cfg.mod env.vars results) conditionEnd = ((yesBlock, joinBlock), forked))
    (forkExtended : ExtT forked cx.fn.blocks)
    (startEq : branchStart = { forked with cur := some yesBlock })
    (branchRun : lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results) branchStart = (value, branchEnd))
    (jumpRun : emitTerm (.br joinBlock []) (lowerEnv cfg.mod env.vars results) branchEnd = ((), jumped))
    (jumpExtended : ExtT jumped cx.fn.blocks) (finalEq : built = { jumped with cur := some joinBlock })
    (joinPoint : built.pp = some (joinBlock, 0)) (joinStack : built.stack = conditionEnd.stack)
    (joinVals : conditionEnd.vals.size ≤ built.vals.size)
    (ended : GeneratedBranchBlockEnd branch map required cx results branchStart loop conditionFrame
      (.normal .unit) ⟨branchPoint, finalFrame, after⟩) :
    (∀ fuel, DemandInstructionStep cx fuel ⟨branchPoint, finalFrame, after⟩ ⟨(joinBlock, 0), finalFrame, after⟩) ∧
      (∃ fuel, execStmt fuel cfg env (.ifS condition yes none origin) state = .ok (.normal .unit) after) ∧
      GeneratedStatementPrefixEnd source map cx before initial built loop (.normal .unit) ⟨(joinBlock, 0), finalFrame, after⟩ := by
  have branchPost : Post cfg env cx branchStart conditionFrame branchEnd finalFrame branchPoint [] := by
    simpa only [branchRun] using ended.post
  obtain ⟨_, _, _, valsEq, _, _, _, _, _⟩ := fork_facts forkRun conditionPost.pp forkExtended
  have startVals : branchStart.vals.size = conditionEnd.vals.size := by rw [startEq]; exact congrArg Array.size valsEq
  have post := generated_if_join_post conditionPost branchPost startVals joinPoint joinStack joinVals
  have jumpAdvance := adv_emitTerm jumpRun
  have bounded : map.Bounded built.vals.size := by
    apply ended.bounded.mono
    rw [branchRun]
    rw [finalEq]
    exact jumpAdvance.vals
  have realized : map.Realizes cfg.mod source.world env ⟨(joinBlock, 0), finalFrame, after⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using ended.demanded.operands
  obtain ⟨fuel, done⟩ := if_then_source_success (no := none) (origin := origin) conditionDone branchDone
  exact ⟨fun fuel => generated_if_join_step forkRun conditionPost.pp forkExtended jumpRun branchPost.pp jumpExtended fuel,
    ⟨fuel, done⟩, .normal post (source.result _ _ done) bounded realized⟩

#print axioms accepted_generated_if_then_join
#print axioms accepted_generated_if_skip
end Goose.Lower
