import Goose.Lower.DemandIfSourceFlow

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_if_none_join_builder {le : LEnv} {before after : LS} {loop : Option LoopCtx}
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
      ExtT forked cx.fn.blocks ∧ ExtT branchEnd cx.fn.blocks ∧ ExtT jumped cx.fn.blocks ∧
      after.pp = some (joinBlock, 0) ∧ after.stack = (lowerExpr condition le before).2.stack ∧
      (lowerExpr condition le before).2.vals.size ≤ after.vals.size := by
  obtain ⟨yesBlock, joinBlock, forked, branchStart, branchEnd, jumped, value, forkRun, startEq,
    branchRun, jumpRun, finalEq, forkExtended, branchExtended⟩ := generated_if_none_fork lowered atPoint extended
  have jumpedExtended : ExtT jumped cx.fn.blocks := by rw [finalEq] at extended; exact extended
  obtain ⟨yesId, joinId, forkSize, _, forkStack, _, _, yesAt, joinAt⟩ := fork_facts forkRun atPoint forkExtended
  have branchAdv := advB_lowerBlock loop [] false yes _ _ _ _ branchRun
  have jumpAdv := adv_emitTerm jumpRun
  have joinStart : branchStart.blocks[joinBlock]? = some ⟨[], #[]⟩ := by rw [startEq]; exact joinAt
  have joinBranch : branchEnd.blocks[joinBlock]? = some ⟨[], #[]⟩ := by
    refine branchAdv.keep joinBlock ⟨[], #[]⟩ ?_ joinStart
    rw [startEq]
    intro same
    have sameIds := Option.some.inj same
    nat_omega
  have joinJumped : jumped.blocks[joinBlock]? = some ⟨[], #[]⟩ := by
    cases current : branchEnd.cur with
    | none =>
      rw [emitTerm_none _ _ current] at jumpRun
      obtain ⟨_, rfl⟩ := Prod.mk.inj jumpRun
      exact joinBranch
    | some currentId =>
      rw [emitTerm_run _ _ current] at jumpRun
      obtain ⟨_, rfl⟩ := Prod.mk.inj jumpRun
      have different : currentId ≠ joinBlock := by
        rcases branchAdv.cur with h | h | ⟨c, hc, hc1, _⟩
        · rw [current] at h; cases h
        · rw [current, startEq] at h
          have same := Option.some.inj h
          nat_omega
        · rw [current] at hc
          have same := Option.some.inj hc
          have size : branchStart.blocks.size = (lowerExpr condition le before).2.blocks.size + 2 := by
            rw [startEq]; exact forkSize
          nat_omega
      show (branchEnd.blocks.modify currentId _)[joinBlock]? = _
      rw [getElem?_modify_ne different]
      exact joinBranch
  have joinPoint : after.pp = some (joinBlock, 0) := by rw [finalEq]; exact LS.pp_cur joinJumped
  have joinStack : after.stack = (lowerExpr condition le before).2.stack := by
    rw [finalEq]
    change jumped.stack = _
    rw [jumpAdv.stack, branchAdv.stack, startEq]
    exact forkStack
  have joinVals : (lowerExpr condition le before).2.vals.size ≤ after.vals.size := by
    rw [finalEq]
    change _ ≤ jumped.vals.size
    have first := branchAdv.vals
    have second := jumpAdv.vals
    have vals := (fork_facts forkRun atPoint forkExtended).2.2.2.1
    rw [startEq] at first
    simp only at first
    rw [vals] at first
    omega
  exact ⟨yesBlock, joinBlock, forked, branchStart, branchEnd, jumped, value, forkRun, startEq,
    branchRun, jumpRun, finalEq, forkExtended, branchExtended, jumpedExtended, joinPoint, joinStack, joinVals⟩

theorem generated_if_join_post {cfg : Cfg} {env : Env} {cx : FnCtx}
    {before conditionEnd branchStart branchEnd after : LS} {initial conditionFrame finalFrame : GIR.Frame}
    {conditionPoint branchPoint : Pt} {conditionCells : List (ValueId × RVal)} {joinBlock : BlockId}
    (conditionPost : Post cfg env cx before initial conditionEnd conditionFrame conditionPoint conditionCells)
    (branchPost : Post cfg env cx branchStart conditionFrame branchEnd finalFrame branchPoint [])
    (branchVals : branchStart.vals.size = conditionEnd.vals.size)
    (joinPoint : after.pp = some (joinBlock, 0)) (joinStack : after.stack = conditionEnd.stack)
    (joinVals : conditionEnd.vals.size ≤ after.vals.size) :
    Post cfg env cx before initial after finalFrame (joinBlock, 0) [] := by
  have same : Same before.vals.size initial finalFrame := conditionPost.same.trans branchPost.same (by
    rw [branchVals]
    exact conditionPost.mono)
  have related : Rel cfg env cx finalFrame after := branchPost.rel.stack_eq (by rw [joinStack, conditionPost.rel.stack, branchPost.rel.stack])
  exact Post.nil joinPoint (Nat.le_trans conditionPost.mono joinVals) same related

theorem generated_if_skip_post {cfg : Cfg} {env : Env} {cx : FnCtx}
    {before conditionEnd after : LS} {initial frame : GIR.Frame} {conditionPoint : Pt}
    {conditionCells : List (ValueId × RVal)} {joinBlock : BlockId}
    (conditionPost : Post cfg env cx before initial conditionEnd frame conditionPoint conditionCells)
    (joinPoint : after.pp = some (joinBlock, 0)) (joinStack : after.stack = conditionEnd.stack)
    (joinVals : conditionEnd.vals.size ≤ after.vals.size) :
    Post cfg env cx before initial after frame (joinBlock, 0) [] := by
  exact Post.nil joinPoint (Nat.le_trans conditionPost.mono joinVals) conditionPost.same
    (conditionPost.rel.stack_eq joinStack)

#print axioms generated_if_join_post
#print axioms generated_if_skip_post
#print axioms generated_if_none_join_builder
end Goose.Lower
