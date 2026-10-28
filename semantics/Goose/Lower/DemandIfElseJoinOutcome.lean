import Goose.Lower.DemandIfElseJoin
import Goose.Lower.DemandIfJoinBuilder

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem if_else_source_success {cfg : Cfg} {env : Env} {condition : Expr} {yes no : Core.Block}
    {origin : OriginId} {state middle after : St} {conditionFuel branchFuel : Nat}
    (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool false) middle)
    (branchDone : execBlock branchFuel cfg env [] no middle = .ok (.normal .unit) after) :
    ∃ fuel, execStmt fuel cfg env (.ifS condition yes (some no) origin) state = .ok (.normal .unit) after := by
  let common := max conditionFuel branchFuel
  have conditionAt := ((monoAll conditionFuel common (Nat.le_max_left _ _)).expr cfg env condition state).1 _ _ conditionDone
  have branchAt := ((monoAll branchFuel common (Nat.le_max_right _ _)).block cfg env [] no middle).1 _ _ branchDone
  refine ⟨common + 1, ?_⟩
  simp only [execStmt, bind_apply, conditionAt, expectBool, pure_apply, Bool.false_eq_true, ite_false, branchAt]

theorem if_else_source_stop {cfg : Cfg} {env : Env} {condition : Expr} {yes no : Core.Block}
    {origin : OriginId} {state middle after : St} {conditionFuel branchFuel : Nat} {stop : Stop}
    (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool false) middle)
    (branchStopped : execBlock branchFuel cfg env [] no middle = .stop stop after) (nonTimeout : stop ≠ .timeout) :
    ∃ fuel, execStmt fuel cfg env (.ifS condition yes (some no) origin) state = .stop stop after := by
  let common := max conditionFuel branchFuel
  have conditionAt := ((monoAll conditionFuel common (Nat.le_max_left _ _)).expr cfg env condition state).1 _ _ conditionDone
  rcases ((monoAll branchFuel common (Nat.le_max_right _ _)).block cfg env [] no middle).2 _ _ branchStopped with timeout | branchAt
  · cases stop <;> simp_all [isTimeout]
  · refine ⟨common + 1, ?_⟩
    simp only [execStmt, bind_apply, conditionAt, expectBool, pure_apply, Bool.false_eq_true, ite_false, branchAt]


theorem accepted_generated_if_some_join {cfg : Cfg} {env : Env} {condition : Expr} {yes no : Core.Block}
    {origin : OriginId} {state middle afterState : St} (source : StmtSource cfg env (.ifS condition yes (some no) origin) state)
    (takeYes : Bool) (branch : BlockSource cfg env [] (if takeYes then yes else no) middle)
    (world : branch.world = source.world) {conditionFuel branchFuel : Nat}
    (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool takeYes) middle)
    (branchDone : execBlock branchFuel cfg env [] (if takeYes then yes else no) middle = .ok (.normal .unit) afterState)
    {cx : FnCtx} {results : List Ty} {before conditionEnd forked yesStart yesEnd noStart noEnd built : LS}
    {loop : Option LoopCtx} {initial conditionFrame finalFrame : GIR.Frame} {conditionPoint branchPoint : Pt}
    {map required : RetainedSsaMap} {conditionId yesBlock noBlock yesValue noValue : Nat}
    {yesEndPoint noEndPoint : Option BlockId}
    (conditionPost : Post cfg env cx before initial conditionEnd conditionFrame conditionPoint [(conditionId, .val (.bool takeYes))])
    (forkRun : fork conditionId (lowerEnv cfg.mod env.vars results) conditionEnd = ((yesBlock, noBlock), forked))
    (forkExtended : ExtT forked cx.fn.blocks)
    (yesStartEq : yesStart = { forked with cur := some yesBlock })
    (yesRun : lowerBlock loop [] false yes (lowerEnv cfg.mod env.vars results) yesStart = (yesValue, yesEnd))
    (yesCurrent : yesEndPoint = yesEnd.cur)
    (noStartEq : noStart = { yesEnd with cur := some noBlock })
    (noRun : lowerBlock loop [] false no (lowerEnv cfg.mod env.vars results) noStart = (noValue, noEnd))
    (noCurrent : noEndPoint = noEnd.cur)
    (joined : joinArms yesEndPoint noEndPoint (lowerEnv cfg.mod env.vars results) noEnd = ((), built))
    (extended : ExtT built cx.fn.blocks)
    (ended : GeneratedBranchBlockEnd branch map required cx results (if takeYes then yesStart else noStart) loop conditionFrame
      (.normal .unit) ⟨branchPoint, finalFrame, afterState⟩) :
    (∀ fuel, DemandInstructionStep cx fuel ⟨branchPoint, finalFrame, afterState⟩ ⟨(noEnd.blocks.size, 0), finalFrame, afterState⟩) ∧
      (∃ fuel, execStmt fuel cfg env (.ifS condition yes (some no) origin) state = .ok (.normal .unit) afterState) ∧
      GeneratedStatementPrefixEnd source map cx before initial built loop (.normal .unit) ⟨(noEnd.blocks.size, 0), finalFrame, afterState⟩ := by
  have selectedRun : (lowerBlock loop [] false (if takeYes then yes else no) (lowerEnv cfg.mod env.vars results)
      (if takeYes then yesStart else noStart)).2 = (if takeYes then yesEnd else noEnd) := by
    cases takeYes <;> simp [yesRun, noRun]
  have branchPost : Post cfg env cx (if takeYes then yesStart else noStart) conditionFrame
      (if takeYes then yesEnd else noEnd) finalFrame branchPoint [] := by
    simpa only [selectedRun] using ended.post
  have ⟨joinPoint, joinStack, joinVals, allVals, step⟩ := generated_if_some_join (frame := finalFrame) (state := afterState)
    takeYes forkRun yesStartEq yesRun yesCurrent noStartEq noRun noCurrent joined conditionPost.pp branchPost.pp extended
  have vals := (fork_facts forkRun conditionPost.pp forkExtended).2.2.2.1
  have yesAdvance := advB_lowerBlock loop [] false yes _ _ _ _ yesRun
  have noAdvance := advB_lowerBlock loop [] false no _ _ _ _ noRun
  have branchVals : conditionEnd.vals.size ≤ (if takeYes then yesStart else noStart).vals.size := by
    cases takeYes
    · simp only [Bool.false_eq_true, ite_false, noStartEq]
      change conditionEnd.vals.size ≤ yesEnd.vals.size
      have size := yesAdvance.vals
      rw [yesStartEq] at size
      change forked.vals.size ≤ yesEnd.vals.size at size
      rw [vals] at size
      exact size
    · simp only [ite_true, yesStartEq]
      change conditionEnd.vals.size ≤ forked.vals.size
      rw [vals]
      exact Nat.le_refl _
  have post := generated_if_branch_post conditionPost branchPost branchVals joinPoint joinStack joinVals
  have bounded : map.Bounded built.vals.size := by
    apply ended.bounded.mono
    rw [selectedRun, allVals]
    cases takeYes
    · simp
    · simp only [ite_true]
      have size := noAdvance.vals
      rw [noStartEq] at size
      exact size
  have realized : map.Realizes cfg.mod source.world env ⟨(noEnd.blocks.size, 0), finalFrame, afterState⟩ := by
    simpa only [RetainedSsaMap.Realizes, world] using ended.demanded.operands
  have sourceDone : ∃ fuel, execStmt fuel cfg env (.ifS condition yes (some no) origin) state = .ok (.normal .unit) afterState := by
    cases takeYes
    · exact if_else_source_success (yes := yes) (origin := origin) conditionDone branchDone
    · exact if_then_source_success (no := some no) (origin := origin) conditionDone branchDone
  obtain ⟨fuel, done⟩ := sourceDone
  exact ⟨step, ⟨fuel, done⟩, .normal post (source.result _ _ done) bounded realized⟩

#print axioms accepted_generated_if_some_join
#print axioms if_else_source_success
#print axioms if_else_source_stop
#print axioms generated_if_branch_post
end Goose.Lower
