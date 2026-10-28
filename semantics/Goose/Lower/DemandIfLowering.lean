import Goose.Lower.DemandIfBranchStep

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_if_none_fork {le : LEnv} {before after : LS} {loop : Option LoopCtx}
    {condition : Expr} {yes : Core.Block} {origin : OriginId} {cx : FnCtx} {point : Pt}
    (lowered : lowerStmt loop (.ifS condition yes none origin) le before = ((), after))
    (atPoint : (lowerExpr condition le before).2.pp = some point)
    (extended : ExtT after cx.fn.blocks) :
    ∃ yesBlock joinBlock forked branchStart branchEnd jumped value,
      fork (lowerExpr condition le before).1 le (lowerExpr condition le before).2 = ((yesBlock, joinBlock), forked) ∧
      branchStart = { forked with cur := some yesBlock } ∧
      lowerBlock loop [] false yes le branchStart = (value, branchEnd) ∧
      emitTerm (.br joinBlock []) le branchEnd = ((), jumped) ∧
      after = { jumped with cur := some joinBlock } ∧
      ExtT forked cx.fn.blocks ∧ ExtT branchEnd cx.fn.blocks := by
  simp only [lowerStmt, bind_eq] at lowered
  obtain ⟨cv, middle, conditionLowered, rest⟩ := lowered
  have cvEq : cv = (lowerExpr condition le before).1 := congrArg Prod.fst conditionLowered.symm
  have middleEq : middle = (lowerExpr condition le before).2 := congrArg Prod.snd conditionLowered.symm
  subst cv
  subst middle
  obtain ⟨block, current, _, _⟩ := LS.pp_some atPoint
  rw [whenLive_some _ _ _ current] at rest
  simp only [bind_eq] at rest
  obtain ⟨⟨yesBlock, joinBlock⟩, forked, forkedRun, _, branchStart, branchSet,
    value, branchEnd, branchRun, _, jumped, jumpRun, joined⟩ := rest
  have startEq : branchStart = { forked with cur := some yesBlock } := by
    rw [setCur_run] at branchSet
    exact (Prod.mk.inj branchSet).2.symm
  have finalEq : after = { jumped with cur := some joinBlock } := by
    rw [setCur_run] at joined
    exact (Prod.mk.inj joined).2.symm
  have jumpedExtended : ExtT jumped cx.fn.blocks := by rw [finalEq] at extended; exact extended
  have branchExtended := jumpedExtended.of_adv (adv_emitTerm jumpRun)
  have startExtended := branchExtended.of_adv (advB_lowerBlock loop [] false yes _ _ _ _ branchRun)
  have forkExtended : ExtT forked cx.fn.blocks := by rw [startEq] at startExtended; exact startExtended
  exact ⟨yesBlock, joinBlock, forked, branchStart, branchEnd, jumped, value,
    forkedRun, startEq, branchRun, jumpRun, finalEq, forkExtended, branchExtended⟩

theorem generated_if_none_condition_branch {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {loop : Option LoopCtx} {condition : Expr} {yes : Core.Block} {origin : OriginId} {before after : LS}
    {initial frame : GIR.Frame} {point : Pt} {state : St} (value : Bool)
    (lowered : lowerStmt loop (.ifS condition yes none origin) (lowerEnv cfg.mod env.vars results) before = ((), after))
    (post : Post cfg env cx before initial (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool value))])
    (extended : ExtT after cx.fn.blocks) :
    ∃ yesBlock joinBlock forked,
      fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (lowerEnv cfg.mod env.vars results)
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 = ((yesBlock, joinBlock), forked) ∧
      ExtT forked cx.fn.blocks ∧
      ∀ fuel, DemandInstructionStep cx fuel ⟨point, frame, state⟩
        ⟨(if value then yesBlock else joinBlock, 0), frame, state⟩ := by
  obtain ⟨yesBlock, joinBlock, forked, _, _, _, _, forkedRun, _, _, _, _, forkExtended, _⟩ :=
    generated_if_none_fork lowered post.pp extended
  have cell := post.has ((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool value)) (by simp)
  exact ⟨yesBlock, joinBlock, forked, forkedRun, forkExtended,
    fun fuel => generated_if_branch_step value forkedRun post.pp forkExtended cell fuel⟩

theorem generated_if_join_step {condition : ValueId} {le : LEnv} {before forked branchEnd jumped : LS}
    {yesBlock joinBlock : BlockId} {conditionPoint branchPoint : Pt} {cx : FnCtx}
    {frame : GIR.Frame} {state : St}
    (forkedRun : fork condition le before = ((yesBlock, joinBlock), forked))
    (conditionAt : before.pp = some conditionPoint) (forkExtended : ExtT forked cx.fn.blocks)
    (jumpRun : emitTerm (.br joinBlock []) le branchEnd = ((), jumped))
    (branchAt : branchEnd.pp = some branchPoint) (jumpExtended : ExtT jumped cx.fn.blocks)
    (fuel : Nat) : DemandInstructionStep cx fuel ⟨branchPoint, frame, state⟩ ⟨(joinBlock, 0), frame, state⟩ := by
  obtain ⟨_, _, _, _, _, _, _, _, joinAt⟩ := fork_facts forkedRun conditionAt forkExtended
  obtain ⟨join, joinBlockAt, joinParams⟩ := forkExtended.params joinAt
  obtain ⟨_, _, _, instruction⟩ := emitTerm_facts jumpRun branchAt jumpExtended
  let branch : DemandBranch := .jump joinBlock []
  have instructionAt : instAt cx.fn branchPoint = some (.term branch.term) := by
    simpa only [instAt_eq, branch, DemandBranch.term] using instruction
  have execution : branch.enter cx.fn frame state = .ok (joinBlock, instsAt cx.fn (joinBlock, 0), frame) state := by
    simp [branch, DemandBranch.enter, mapList, enterBlock, joinBlockAt, joinParams, bindParams, instsAt, bind_apply, pure_apply]
  exact .control instructionAt execution

#print axioms generated_if_join_step
#print axioms generated_if_none_condition_branch
#print axioms generated_if_none_fork
end Goose.Lower
