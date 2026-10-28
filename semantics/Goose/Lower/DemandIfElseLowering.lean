import Goose.Lower.Claims

namespace Goose.Lower
open Goose.Core Goose.GIR

theorem generated_if_some_fork {le : LEnv} {before after : LS} {loop : Option LoopCtx}
    {condition : Expr} {yes no : Core.Block} {origin : OriginId} {cx : FnCtx} {point : Pt}
    (lowered : lowerStmt loop (.ifS condition yes (some no) origin) le before = ((), after))
    (atPoint : (lowerExpr condition le before).2.pp = some point)
    (extended : ExtT after cx.fn.blocks) :
    ∃ yesBlock noBlock forked yesStart yesEnd noStart noEnd yesValue noValue yesEndPoint noEndPoint,
      fork (lowerExpr condition le before).1 le (lowerExpr condition le before).2 = ((yesBlock, noBlock), forked) ∧
      yesStart = { forked with cur := some yesBlock } ∧
      lowerBlock loop [] false yes le yesStart = (yesValue, yesEnd) ∧
      yesEndPoint = yesEnd.cur ∧ noStart = { yesEnd with cur := some noBlock } ∧
      lowerBlock loop [] false no le noStart = (noValue, noEnd) ∧ noEndPoint = noEnd.cur ∧
      joinArms yesEndPoint noEndPoint le noEnd = ((), after) ∧
      ExtT forked cx.fn.blocks ∧ ExtT yesEnd cx.fn.blocks ∧ ExtT noEnd cx.fn.blocks := by
  simp only [lowerStmt, bind_eq] at lowered
  obtain ⟨cv, middle, conditionLowered, rest⟩ := lowered
  have cvEq : cv = (lowerExpr condition le before).1 := congrArg Prod.fst conditionLowered.symm
  have middleEq : middle = (lowerExpr condition le before).2 := congrArg Prod.snd conditionLowered.symm
  subst cv
  subst middle
  obtain ⟨block, current, _, _⟩ := LS.pp_some atPoint
  rw [whenLive_some _ _ _ current] at rest
  simp only [bind_eq] at rest
  obtain ⟨⟨yesBlock, noBlock⟩, forked, forkRun, _, yesStart, yesSet, yesValue, yesEnd, yesRun,
    yesEndPoint, afterYes, yesCur, _, noStart, noSet, noValue, noEnd, noRun, noEndPoint, afterNo, noCur, joined⟩ := rest
  obtain ⟨yesCurrent, yesSame⟩ := curBlock_eq yesCur
  subst afterYes
  obtain ⟨noCurrent, noSame⟩ := curBlock_eq noCur
  subst afterNo
  have yesStartEq : yesStart = { forked with cur := some yesBlock } := by
    rw [setCur_run] at yesSet
    exact (Prod.mk.inj yesSet).2.symm
  have noStartEq : noStart = { yesEnd with cur := some noBlock } := by
    rw [setCur_run] at noSet
    exact (Prod.mk.inj noSet).2.symm
  have noExtended : ExtT noEnd cx.fn.blocks := extended.of_ext (joinArms_ext joined)
  have noAdvance := advB_lowerBlock loop [] false no _ _ _ _ noRun
  have yesAdvance := advB_lowerBlock loop [] false yes _ _ _ _ yesRun
  have noStartExtended := noExtended.of_adv noAdvance
  have yesExtended : ExtT yesEnd cx.fn.blocks := by rw [noStartEq] at noStartExtended; exact noStartExtended
  have yesStartExtended := yesExtended.of_adv yesAdvance
  have forkExtended : ExtT forked cx.fn.blocks := by rw [yesStartEq] at yesStartExtended; exact yesStartExtended
  exact ⟨yesBlock, noBlock, forked, yesStart, yesEnd, noStart, noEnd, yesValue, noValue, yesEndPoint, noEndPoint,
    forkRun, yesStartEq, yesRun, yesCurrent, noStartEq, noRun, noCurrent, joined, forkExtended, yesExtended, noExtended⟩

#print axioms generated_if_some_fork
end Goose.Lower
