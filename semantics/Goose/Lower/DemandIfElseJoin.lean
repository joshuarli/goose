import Goose.Lower.DemandIfElseInput

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_if_some_join {le : LEnv} {conditionId : ValueId} {before forked yesStart yesEnd noStart noEnd after : LS}
    {yes no : Core.Block} {loop : Option LoopCtx} {yesBlock noBlock yesValue noValue : Nat}
    {yesEndPoint noEndPoint : Option BlockId} {conditionPoint point : Pt} {cx : FnCtx}
    {frame : GIR.Frame} {state : St} (takeYes : Bool)
    (forkRun : fork conditionId le before = ((yesBlock, noBlock), forked))
    (yesStartEq : yesStart = { forked with cur := some yesBlock })
    (yesRun : lowerBlock loop [] false yes le yesStart = (yesValue, yesEnd))
    (yesCurrent : yesEndPoint = yesEnd.cur)
    (noStartEq : noStart = { yesEnd with cur := some noBlock })
    (noRun : lowerBlock loop [] false no le noStart = (noValue, noEnd))
    (noCurrent : noEndPoint = noEnd.cur)
    (joined : joinArms yesEndPoint noEndPoint le noEnd = ((), after))
    (conditionAt : before.pp = some conditionPoint)
    (selectedAt : (if takeYes then yesEnd else noEnd).pp = some point)
    (extended : ExtT after cx.fn.blocks) :
    after.pp = some (noEnd.blocks.size, 0) ∧ after.stack = before.stack ∧ before.vals.size ≤ after.vals.size ∧ after.vals.size = noEnd.vals.size ∧
      ∀ fuel, DemandInstructionStep cx fuel ⟨point, frame, state⟩ ⟨(noEnd.blocks.size, 0), frame, state⟩ := by
  have yesSet : setCur (some yesBlock) le forked = ((), yesStart) := by rw [setCur_run, yesStartEq]
  have noSet : setCur (some noBlock) le yesEnd = ((), noStart) := by rw [setCur_run, noStartEq]
  have noExtended : ExtT noEnd cx.fn.blocks := extended.of_ext (joinArms_ext joined)
  have yesAdvance := advB_lowerBlock loop [] false yes _ _ _ _ yesRun
  have noAdvance := advB_lowerBlock loop [] false no _ _ _ _ noRun
  have noStartExtended := noExtended.of_adv noAdvance
  have yesEndExtended : ExtT yesEnd cx.fn.blocks := by rw [noStartEq] at noStartExtended; exact noStartExtended
  have yesStartExtended := yesEndExtended.of_adv yesAdvance
  have forkExtended : ExtT forked cx.fn.blocks := by rw [yesStartEq] at yesStartExtended; exact yesStartExtended
  obtain ⟨yesId, noId, _, _, _, _, _, _, _, _, noStack, _, _, yesEnds, noEnds, keep, size, _⟩ :=
    branch_facts forkRun yesSet yesAdvance noSet noAdvance conditionAt noExtended
  have yesBound : ∀ b, yesEndPoint = some b → b < noEnd.blocks.size := by
    intro b current
    have fact := yesEnds b (yesCurrent.symm.trans current)
    exact Nat.lt_of_lt_of_le fact.1 size
  have noBound : ∀ b, noEndPoint = some b → b < noEnd.blocks.size := by
    intro b current
    exact (noEnds b (noCurrent.symm.trans current)).1
  have distinct : ∀ y n, yesEndPoint = some y → noEndPoint = some n → y ≠ n := by
    intro y n yesAt noAt equal
    subst n
    obtain ⟨_, notNo, yesCase⟩ := yesEnds y (yesCurrent.symm.trans yesAt)
    obtain ⟨_, noCase⟩ := noEnds y (noCurrent.symm.trans noAt)
    rcases noCase with same | later
    · exact notNo same
    · nat_omega
  cases takeYes with
  | false =>
    obtain ⟨block, current, blockAt, pointEq⟩ := LS.pp_some selectedAt
    have endAt : noEndPoint = some point.1 := noCurrent.trans current
    have live : yesEndPoint.isSome ∨ noEndPoint.isSome := Or.inr (by rw [endAt]; rfl)
    obtain ⟨values, stack, joinAt, joinCur, instruction⟩ := joinArms_facts joined extended live distinct yesBound noBound
    obtain ⟨join, joinBlockAt, joinParams⟩ := extended.params joinAt
    have inst : instAt cx.fn point = some (.term (.br noEnd.blocks.size [])) := by
      have hit := instruction point.1 block (Or.inr endAt) blockAt
      have point' : point = (point.1, block.insts.size) := Prod.ext rfl pointEq
      rw [point']
      exact hit
    let branch : DemandBranch := .jump noEnd.blocks.size []
    have branchAt : instAt cx.fn point = some (.term branch.term) := by simpa [branch, DemandBranch.term] using inst
    have execution : branch.enter cx.fn frame state = .ok (noEnd.blocks.size, instsAt cx.fn (noEnd.blocks.size, 0), frame) state := by
      simp [branch, DemandBranch.enter, mapList, enterBlock, joinBlockAt, joinParams, bindParams, instsAt, bind_apply, pure_apply]
    refine ⟨LS.pp_eq joinCur joinAt, stack.trans noStack, ?_, values, fun fuel => .control branchAt execution⟩
    have advance := noAdvance.vals
    have previous := yesAdvance.vals
    rw [values]
    rw [noStartEq] at advance
    rw [yesStartEq] at previous
    have vals := (fork_facts forkRun conditionAt forkExtended).2.2.2.1
    rw [vals] at previous
    omega
  | true =>
    obtain ⟨block, current, blockAt, pointEq⟩ := LS.pp_some selectedAt
    have endAt : yesEndPoint = some point.1 := yesCurrent.trans current
    have live : yesEndPoint.isSome ∨ noEndPoint.isSome := Or.inl (by rw [endAt]; rfl)
    obtain ⟨values, stack, joinAt, joinCur, instruction⟩ := joinArms_facts joined extended live distinct yesBound noBound
    have notNo := (yesEnds point.1 current).2.1
    have blockAtEnd := keep point.1 block blockAt notNo
    obtain ⟨join, joinBlockAt, joinParams⟩ := extended.params joinAt
    have inst : instAt cx.fn point = some (.term (.br noEnd.blocks.size [])) := by
      have hit := instruction point.1 block (Or.inl endAt) blockAtEnd
      have point' : point = (point.1, block.insts.size) := Prod.ext rfl pointEq
      rw [point']
      exact hit
    let branch : DemandBranch := .jump noEnd.blocks.size []
    have branchAt : instAt cx.fn point = some (.term branch.term) := by simpa [branch, DemandBranch.term] using inst
    have execution : branch.enter cx.fn frame state = .ok (noEnd.blocks.size, instsAt cx.fn (noEnd.blocks.size, 0), frame) state := by
      simp [branch, DemandBranch.enter, mapList, enterBlock, joinBlockAt, joinParams, bindParams, instsAt, bind_apply, pure_apply]
    refine ⟨LS.pp_eq joinCur joinAt, stack.trans noStack, ?_, values, fun fuel => .control branchAt execution⟩
    have advance := noAdvance.vals
    have previous := yesAdvance.vals
    rw [values]
    rw [noStartEq] at advance
    rw [yesStartEq] at previous
    have vals := (fork_facts forkRun conditionAt forkExtended).2.2.2.1
    rw [vals] at previous
    omega

#print axioms generated_if_some_join
end Goose.Lower
