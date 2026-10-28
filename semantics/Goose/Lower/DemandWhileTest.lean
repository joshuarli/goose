import Goose.Lower.DemandWhileConditionPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_while_test_fork {le : LEnv} {header : BlockId} {before after : LS}
    {condition : Expr} {body : Core.Block} {cx : FnCtx} {point : Pt}
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body) le before = ((), after))
    (atPoint : (lowerExpr condition le before).2.pp = some point)
    (extended : ExtT after cx.fn.blocks) :
    ∃ bodyBlock exitBlock forked bodyStart bodyEnd jumped value,
      fork (lowerExpr condition le before).1 le (lowerExpr condition le before).2 = ((bodyBlock, exitBlock), forked) ∧
      bodyStart = { forked with cur := some bodyBlock } ∧
      lowerBlock (some ⟨(lowerExpr condition le before).2.stack.length, exitBlock, .jump header⟩) [] false body le bodyStart = (value, bodyEnd) ∧
      emitTerm (.br header []) le bodyEnd = ((), jumped) ∧
      after = { jumped with cur := some exitBlock } ∧
      ExtT forked cx.fn.blocks ∧ ExtT bodyEnd cx.fn.blocks ∧ ExtT jumped cx.fn.blocks := by
  simp only [lowerWhile, bind_eq] at lowered
  obtain ⟨cv, middle, conditionRun, rest⟩ := lowered
  have cvEq : cv = (lowerExpr condition le before).1 := congrArg Prod.fst conditionRun.symm
  have middleEq : middle = (lowerExpr condition le before).2 := congrArg Prod.snd conditionRun.symm
  subst cv
  subst middle
  obtain ⟨block, current, _, _⟩ := LS.pp_some atPoint
  rw [whenLive_some _ _ _ current] at rest
  unfold loopBody at rest
  simp only [bind_eq] at rest
  obtain ⟨st, afterGet, getRun, ⟨bodyBlock, exitBlock⟩, forked, forkRun,
    _, bodyStart, bodySet, value, bodyEnd, bodyRun, _, jumped, jumpRun, finalSet⟩ := rest
  rw [get_apply] at getRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj getRun
  have bodyEq : bodyStart = { forked with cur := some bodyBlock } := by
    rw [setCur_run] at bodySet
    exact (Prod.mk.inj bodySet).2.symm
  have finalEq : after = { jumped with cur := some exitBlock } := by
    rw [setCur_run] at finalSet
    exact (Prod.mk.inj finalSet).2.symm
  have jumpedExtended : ExtT jumped cx.fn.blocks := by rw [finalEq] at extended; exact extended
  have bodyExtended := jumpedExtended.of_adv (adv_emitTerm jumpRun)
  have startExtended := bodyExtended.of_adv (advB_lowerBlock _ [] false body _ _ _ _ bodyRun)
  have forkExtended : ExtT forked cx.fn.blocks := by rw [bodyEq] at startExtended; exact startExtended
  exact ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, value,
    forkRun, bodyEq, bodyRun, jumpRun, finalEq, forkExtended, bodyExtended, jumpedExtended⟩

theorem generated_while_test_branch {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {header : BlockId} {before after : LS} {condition : Expr} {body : Core.Block}
    {initial frame : GIR.Frame} {point : Pt} {state : St} (value : Bool)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) before = ((), after))
    (post : Post cfg env cx before initial (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool value))])
    (extended : ExtT after cx.fn.blocks) :
    ∃ bodyBlock exitBlock forked bodyStart bodyEnd jumped bodyValue,
      fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (lowerEnv cfg.mod env.vars results)
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 = ((bodyBlock, exitBlock), forked) ∧
      bodyStart = { forked with cur := some bodyBlock } ∧
      lowerBlock (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.stack.length, exitBlock, .jump header⟩)
        [] false body (lowerEnv cfg.mod env.vars results) bodyStart = (bodyValue, bodyEnd) ∧
      emitTerm (.br header []) (lowerEnv cfg.mod env.vars results) bodyEnd = ((), jumped) ∧
      after = { jumped with cur := some exitBlock } ∧ ExtT forked cx.fn.blocks ∧
      ExtT bodyEnd cx.fn.blocks ∧ ExtT jumped cx.fn.blocks ∧
      ∀ fuel, DemandInstructionStep cx fuel ⟨point, frame, state⟩
        ⟨(if value then bodyBlock else exitBlock, 0), frame, state⟩ := by
  obtain ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, bodyValue,
    forkRun, bodyEq, bodyRun, jumpRun, finalEq, forkExtended, bodyExtended, jumpExtended⟩ :=
    generated_while_test_fork lowered post.pp extended
  have cell := post.has ((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool value)) (by simp)
  exact ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, bodyValue,
    forkRun, bodyEq, bodyRun, jumpRun, finalEq, forkExtended, bodyExtended, jumpExtended,
    fun fuel => generated_if_branch_step value forkRun post.pp forkExtended cell fuel⟩

#print axioms generated_while_test_fork
#print axioms generated_while_test_branch
end Goose.Lower
