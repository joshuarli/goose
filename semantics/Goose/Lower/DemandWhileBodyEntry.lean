import Goose.Lower.DemandWhileTest

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_body_entry {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state middle : St} (source : StmtSource cfg env (.while condition body origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {fuel : Nat} (evaluated : evalExpr fuel cfg env condition state = .ok (.bool true) middle)
    {cx : FnCtx} {results : List Ty} {loop : Option LoopCtx} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context) {before headerState forked bodyStart : LS}
    {header bodyBlock exitBlock : BlockId} {initial frame : GIR.Frame} {point : Pt}
    (headerId : header = (newBlock [] (lowerEnv cfg.mod env.vars results) before).1.1)
    (headerEq : headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (boundary : ExpressionDemandBoundary child map cx headerState initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1 (.bool true) middle point frame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2 =
      ((bodyBlock, exitBlock), forked))
    (bodyEq : bodyStart = { forked with cur := some bodyBlock }) (extended : ExtT forked cx.fn.blocks) :
    ∃ branch : BlockSource cfg env [] body middle,
      branch.typingEnv = { source.typingEnv with loops := source.typingEnv.loops + 1 } ∧
      branch.rootsEnv = source.rootsEnv ∧ source.BlockChildAt branch 1 (by simp [DemandNode.child?, DemandNode.children]) ∧
      GeneratedSourceOwner selected branch.context ∧ map.Admitted cfg.mod.profile branch.context.retained ∧
      map.Bounded bodyStart.vals.size ∧ map.Realizes cfg.mod branch.world env ⟨(bodyBlock, 0), frame, middle⟩ ∧
      ∃ branchOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root branch.path (.block (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length,
          exitBlock, .jump header⟩) [] false body) bodyStart,
        GeneratedDemandRows cfg.mod branch.rootsEnv.access branchOccurrence required := by
  obtain ⟨branch, typing, roots, world, observation, branchCanonical⟩ := source.whileBodyChildAt fuel evaluated
  have branchOwner : GeneratedSourceOwner selected branch.context :=
    (owned.child rfl 1 (.block body) .block (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).transport
      branchCanonical.plans.symm branchCanonical.path.symm rfl branchCanonical.context.symm
  have branchAdmitted : map.Admitted cfg.mod.profile branch.context.retained := by
    rw [demandContextRetainedEq branchCanonical.plans branchCanonical.path rfl branchCanonical.context]
    intro profile alias member
    exact source.context.child_retained_subset rfl 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children]) (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
      (admitted profile alias member)
  obtain ⟨_, _, _, valsEq, _, _, _, _, _⟩ := fork_facts forkRun boundary.post.pp extended
  have branchBounded : map.Bounded bodyStart.vals.size := by
    rw [bodyEq]
    change map.Bounded forked.vals.size
    rw [valsEq]
    exact boundary.bounded
  have branchRealized : map.Realizes cfg.mod branch.world env ⟨(bodyBlock, 0), frame, middle⟩ := by
    simpa only [RetainedSsaMap.Realizes, world, canonical.world] using boundary.demanded.operands
  obtain ⟨_, current, _, _⟩ := LS.pp_some boundary.post.pp
  have live : (demandWhileTest condition (lowerEnv cfg.mod env.vars results) before).2.cur.isSome = true := by
    unfold demandWhileTest
    rw [← headerEq, current]
    rfl
  have inherited : ∃ bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root (source.path ++ [1])
      (.block (some ⟨(demandWhileTest condition (lowerEnv cfg.mod env.vars results) before).2.stack.length,
        (demandWhileFork condition (lowerEnv cfg.mod env.vars results) before).1.2,
        .jump (newBlock [] (lowerEnv cfg.mod env.vars results) before).1.1⟩) [] false body)
      { (demandWhileFork condition (lowerEnv cfg.mod env.vars results) before).2 with
        cur := some (demandWhileFork condition (lowerEnv cfg.mod env.vars results) before).1.1 },
      GeneratedDemandRows cfg.mod source.rootsEnv.access bodyOccurrence required :=
    ⟨.whileBody occurrence live, .whileBody (live := live) rows⟩
  have childRows : ∃ bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root branch.path (.block (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length,
        exitBlock, .jump header⟩) [] false body) bodyStart,
      GeneratedDemandRows cfg.mod branch.rootsEnv.access bodyOccurrence required := by
    rw [branchCanonical.path, roots, bodyEq, headerId]
    simpa only [demandWhileFork, demandWhileTest, ← headerEq, forkRun] using inherited
  exact ⟨branch, typing, roots, branchCanonical, branchOwner, branchAdmitted, branchBounded, branchRealized, childRows⟩

#print axioms accepted_generated_while_body_entry
end Goose.Lower
