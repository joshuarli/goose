import Goose.Lower.DemandIfElseJoinOutcome

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_if_selected_input {cfg : Cfg} {env : Env} {condition : Expr} {yes no : Core.Block}
    {origin : OriginId} {state middle : St}
    (source : StmtSource cfg env (.ifS condition yes (some no) origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    (takeYes : Bool) {sourceFuel : Nat}
    (evaluated : evalExpr sourceFuel cfg env condition state = .ok (.bool takeYes) middle)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    {before forked yesStart yesEnd noStart : LS} {initial frame : GIR.Frame} {start point : Pt}
    {map required : RetainedSsaMap} {loop : Option LoopCtx} {yesBlock noBlock value : Nat}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.ifS condition yes (some no) origin)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (boundary : ExpressionDemandBoundary child map cx before initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (.bool takeYes) middle point frame)
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 =
      ((yesBlock, noBlock), forked))
    (forkExtended : ExtT forked cx.fn.blocks) (yesStartEq : yesStart = { forked with cur := some yesBlock })
    (yesRun : lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results) yesStart = (value, yesEnd))
    (noStartEq : noStart = { yesEnd with cur := some noBlock }) :
    ∃ branch : BlockSource cfg env [] (if takeYes then yes else no) middle,
      branch.world = source.world ∧ GeneratedSourceOwner selected branch.context ∧
      map.Admitted cfg.mod.profile branch.context.retained ∧ map.Bounded (if takeYes then yesStart else noStart).vals.size ∧
      map.Realizes cfg.mod branch.world env ⟨(if takeYes then yesBlock else noBlock, 0), frame, middle⟩ ∧
      GeneratedPrefixInput cfg env cx results loop branch.typingEnv branch.rootsEnv (if takeYes then yesStart else noStart)
        frame (if takeYes then yesBlock else noBlock, 0) ∧
      ∃ branchOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root branch.path (.block loop [] false (if takeYes then yes else no)) (if takeYes then yesStart else noStart),
        GeneratedDemandRows cfg.mod branch.rootsEnv.access branchOccurrence required := by
  cases takeYes with
  | false =>
    obtain ⟨branch, typing, roots, branchCanonical, owner, branchAdmitted, bounded, realized, branchInput⟩ :=
      accepted_generated_if_else_input source child canonical evaluated selected owned admitted input boundary forkRun yesStartEq yesRun noStartEq forkExtended
    obtain ⟨branchOccurrence, branchRows⟩ := generated_if_else_occurrence source branch branchCanonical occurrence rows
      boundary.post.pp forkRun yesStartEq yesRun noStartEq roots
    exact ⟨branch, branchCanonical.world, owner, branchAdmitted, bounded, realized, branchInput, branchOccurrence, branchRows⟩
  | true =>
    obtain ⟨branch, typing, roots, branchCanonical, owner, branchAdmitted, bounded, realized, branchInput⟩ :=
      accepted_generated_if_then_input source child canonical evaluated selected owned admitted input boundary forkRun yesStartEq forkExtended
    obtain ⟨branchOccurrence, branchRows⟩ := generated_if_then_occurrence source branch branchCanonical occurrence rows
      boundary.post.pp forkRun yesStartEq roots
    exact ⟨branch, branchCanonical.world, owner, branchAdmitted, bounded, realized, branchInput, branchOccurrence, branchRows⟩

#print axioms accepted_generated_if_selected_input
end Goose.Lower
