import Goose.Lower.DemandWhileBodyInput

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_body_ready {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state middle : St} (source : StmtSource cfg env (.while condition body origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {fuel : Nat} (evaluated : evalExpr fuel cfg env condition state = .ok (.bool true) middle)
    {cx : FnCtx} {results : List Ty} {loop : Option LoopCtx} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context) {before headerState forked bodyStart : LS}
    {header bodyBlock exitBlock : BlockId} {initial frame : GIR.Frame} {point : Pt}
    (headerInput : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv headerState initial (header, 0))
    (headerTarget : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = [])
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
        GeneratedDemandRows cfg.mod branch.rootsEnv.access branchOccurrence required ∧
        GeneratedPrefixInput cfg env cx results
          (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
          branch.typingEnv branch.rootsEnv bodyStart frame (bodyBlock, 0) := by
  obtain ⟨branch, typing, roots, canonicalBranch, branchOwner, branchAdmitted, branchBounded, branchRealized, branchOccurrence, branchRows⟩ :=
    accepted_generated_while_body_entry source child canonical evaluated selected owned headerId headerEq occurrence rows admitted boundary forkRun bodyEq extended
  have branchInput := generated_while_body_input source child branch typing roots headerInput headerTarget boundary forkRun bodyEq extended
  exact ⟨branch, typing, roots, canonicalBranch, branchOwner, branchAdmitted, branchBounded, branchRealized, branchOccurrence, branchRows, branchInput⟩

#print axioms accepted_generated_while_body_ready
end Goose.Lower
