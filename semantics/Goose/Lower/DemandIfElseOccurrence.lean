import Goose.Lower.DemandIfBranchOccurrence
import Goose.Lower.DemandIfElseLowering

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_if_else_occurrence {cfg : Cfg} {env : Env} {condition : Expr} {yes no : Core.Block}
    {origin : OriginId} {state middle : St}
    (source : StmtSource cfg env (.ifS condition yes (some no) origin) state)
    (branch : BlockSource cfg env [] no middle)
    (canonical : source.BlockChildAt branch 2 (by simp [DemandNode.child?, DemandNode.children]))
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before forked yesStart yesEnd noStart : LS}
    {loop : Option LoopCtx} {yesBlock noBlock value : Nat} {point : Pt}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.ifS condition yes (some no) origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (pointAt : (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.pp = some point)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, noBlock), forked))
    (yesStartEq : yesStart = { forked with cur := some yesBlock })
    (yesRun : lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results) yesStart = (value, yesEnd))
    (noStartEq : noStart = { yesEnd with cur := some noBlock })
    (roots : branch.rootsEnv = source.rootsEnv) :
    ∃ branchOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root branch.path (.block loop [] false no) noStart,
      GeneratedDemandRows cfg.mod branch.rootsEnv.access branchOccurrence required := by
  obtain ⟨_, current, _, _⟩ := LS.pp_some pointAt
  have live : (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.cur.isSome = true := by simp [current]
  rw [noStartEq, canonical.path, roots]
  have built : ∃ child : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root (source.path ++ [2]) (.block loop [] false no)
      { (lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results)
          { (fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
              (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2).2 with
            cur := some (fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
              (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2).1.1 }).2 with
        cur := some (fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
          (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2).1.2 },
      GeneratedDemandRows cfg.mod source.rootsEnv.access child required :=
    ⟨.ifElse occurrence live, .ifElse (live := live) rows⟩
  rw [yesStartEq] at yesRun
  simpa only [forkRun, yesRun] using built

#print axioms generated_if_else_occurrence
end Goose.Lower
