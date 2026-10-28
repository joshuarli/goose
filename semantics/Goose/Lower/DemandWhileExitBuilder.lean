import Goose.Lower.DemandWhileTest

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_while_exit_builder {le : LEnv} {header : BlockId} {before after : LS}
    {condition : Expr} {body : Core.Block} {cx : FnCtx} {point : Pt}
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body) le before = ((), after))
    (atPoint : (lowerExpr condition le before).2.pp = some point) (extended : ExtT after cx.fn.blocks) :
    ∃ bodyBlock exitBlock forked bodyStart bodyEnd jumped value,
      fork (lowerExpr condition le before).1 le (lowerExpr condition le before).2 = ((bodyBlock, exitBlock), forked) ∧
      bodyStart = { forked with cur := some bodyBlock } ∧
      lowerBlock (some ⟨(lowerExpr condition le before).2.stack.length, exitBlock, .jump header⟩) [] false body le bodyStart = (value, bodyEnd) ∧
      emitTerm (.br header []) le bodyEnd = ((), jumped) ∧ after = { jumped with cur := some exitBlock } ∧
      ExtT forked cx.fn.blocks ∧ ExtT bodyEnd cx.fn.blocks ∧ ExtT jumped cx.fn.blocks ∧
      after.pp = some (exitBlock, 0) ∧ after.stack = (lowerExpr condition le before).2.stack ∧
      (lowerExpr condition le before).2.vals.size ≤ after.vals.size := by
  obtain ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, value, forkRun, bodyEq,
    bodyRun, jumpRun, finalEq, forkExtended, bodyExtended, jumpedExtended⟩ := generated_while_test_fork lowered atPoint extended
  obtain ⟨bodyId, exitId, forkSize, _, forkStack, _, _, yesAt, exitAt⟩ := fork_facts forkRun atPoint forkExtended
  have bodyAdv := advB_lowerBlock (some ⟨(lowerExpr condition le before).2.stack.length, exitBlock, .jump header⟩) [] false body _ _ _ _ bodyRun
  have jumpAdv := adv_emitTerm jumpRun
  have exitStart : bodyStart.blocks[exitBlock]? = some ⟨[], #[]⟩ := by rw [bodyEq]; exact exitAt
  have exitBranch : bodyEnd.blocks[exitBlock]? = some ⟨[], #[]⟩ := by
    refine bodyAdv.keep exitBlock ⟨[], #[]⟩ ?_ exitStart
    rw [bodyEq]
    intro same
    have sameIds := Option.some.inj same
    nat_omega
  have exitJumped : jumped.blocks[exitBlock]? = some ⟨[], #[]⟩ := by
    cases current : bodyEnd.cur with
    | none =>
      rw [emitTerm_none _ _ current] at jumpRun
      obtain ⟨_, rfl⟩ := Prod.mk.inj jumpRun
      exact exitBranch
    | some currentId =>
      rw [emitTerm_run _ _ current] at jumpRun
      obtain ⟨_, rfl⟩ := Prod.mk.inj jumpRun
      have different : currentId ≠ exitBlock := by
        rcases bodyAdv.cur with h | h | ⟨c, hc, hc1, _⟩
        · rw [current] at h; cases h
        · rw [current, bodyEq] at h
          have same := Option.some.inj h
          nat_omega
        · rw [current] at hc
          have same := Option.some.inj hc
          have size : bodyStart.blocks.size = (lowerExpr condition le before).2.blocks.size + 2 := by
            rw [bodyEq]; exact forkSize
          nat_omega
      show (bodyEnd.blocks.modify currentId _)[exitBlock]? = _
      rw [getElem?_modify_ne different]
      exact exitBranch
  have exitPoint : after.pp = some (exitBlock, 0) := by rw [finalEq]; exact LS.pp_cur exitJumped
  have exitStack : after.stack = (lowerExpr condition le before).2.stack := by
    rw [finalEq]
    change jumped.stack = _
    rw [jumpAdv.stack, bodyAdv.stack, bodyEq]
    exact forkStack
  have exitVals : (lowerExpr condition le before).2.vals.size ≤ after.vals.size := by
    rw [finalEq]
    change _ ≤ jumped.vals.size
    have first := bodyAdv.vals
    have second := jumpAdv.vals
    have vals := (fork_facts forkRun atPoint forkExtended).2.2.2.1
    rw [bodyEq] at first
    simp only at first
    rw [vals] at first
    omega
  exact ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, value, forkRun, bodyEq,
    bodyRun, jumpRun, finalEq, forkExtended, bodyExtended, jumpedExtended, exitPoint, exitStack, exitVals⟩

#print axioms generated_while_exit_builder
end Goose.Lower
