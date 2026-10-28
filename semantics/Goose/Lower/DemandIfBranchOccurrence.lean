import Goose.Lower.DemandIfBranchInput

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_if_then_occurrence {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {no : Option Core.Block} {origin : OriginId} {state middle : St}
    (source : StmtSource cfg env (.ifS condition yes no origin) state)
    (branch : BlockSource cfg env [] yes middle)
    (canonical : source.BlockChildAt branch 1 (by simp [DemandNode.child?, DemandNode.children]))
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before forked branchStart : LS}
    {loop : Option LoopCtx} {yesBlock noBlock : BlockId} {point : Pt}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.ifS condition yes no origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (pointAt : (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.pp = some point)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, noBlock), forked))
    (startEq : branchStart = { forked with cur := some yesBlock })
    (roots : branch.rootsEnv = source.rootsEnv) :
    ∃ branchOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root branch.path (.block loop [] false yes) branchStart,
      GeneratedDemandRows cfg.mod branch.rootsEnv.access branchOccurrence required := by
  obtain ⟨_, current, _, _⟩ := LS.pp_some pointAt
  have live : (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.cur.isSome = true := by simp [current]
  rw [startEq, canonical.path, roots]
  have built : ∃ child : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root (source.path ++ [1]) (.block loop [] false yes)
      { (fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
          (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2).2 with
        cur := some (fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
          (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2).1.1 },
      GeneratedDemandRows cfg.mod source.rootsEnv.access child required :=
    ⟨.ifThen occurrence live, .ifThen (live := live) rows⟩
  simpa only [forkRun] using built

#print axioms generated_if_then_occurrence
end Goose.Lower
