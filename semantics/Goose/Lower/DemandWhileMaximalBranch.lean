import Goose.Lower.DemandWhileTest

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_while_maximal_condition_branch {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {header : BlockId} {before after : LS} {condition : Expr} {body : Core.Block}
    {initial frame : GIR.Frame} {point : Pt} {state : St} (value : Bool)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) before = ((), after))
    (post : Post cfg env cx before initial (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool value))])
    (extended : ExtT after cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨point, frame, state⟩ reached)
    {fuel : Nat} (maximal : ∀ next, ¬ DemandInstructionStep cx fuel reached next) :
    ∃ bodyBlock exitBlock forked bodyStart bodyEnd jumped bodyValue remaining,
      fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (lowerEnv cfg.mod env.vars results)
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 = ((bodyBlock, exitBlock), forked) ∧
      bodyStart = { forked with cur := some bodyBlock } ∧
      lowerBlock (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.stack.length, exitBlock, .jump header⟩)
        [] false body (lowerEnv cfg.mod env.vars results) bodyStart = (bodyValue, bodyEnd) ∧
      emitTerm (.br header []) (lowerEnv cfg.mod env.vars results) bodyEnd = ((), jumped) ∧
      after = { jumped with cur := some exitBlock } ∧ ExtT forked cx.fn.blocks ∧
      ExtT bodyEnd cx.fn.blocks ∧ ExtT jumped cx.fn.blocks ∧ taken = remaining + 1 ∧
      DemandRuntimePrefix cx remaining ⟨(if value then bodyBlock else exitBlock, 0), frame, state⟩ reached := by
  obtain ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, bodyValue,
    forkRun, bodyEq, bodyRun, jumpRun, finalEq, forkExtended, bodyExtended, jumpExtended, branchStep⟩ :=
    generated_while_test_branch value lowered post extended
  rcases steps.uncons with ⟨zero, rfl⟩ | ⟨remaining, next, count, first, residual⟩
  · exact (maximal _ (branchStep fuel)).elim
  · obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep first
    have equal := actual.deterministic (branchStep stepFuel)
    have nextEq : next = ⟨(if value then bodyBlock else exitBlock, 0), frame, state⟩ := by cases next; exact equal
    subst next
    exact ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, bodyValue, remaining,
      forkRun, bodyEq, bodyRun, jumpRun, finalEq, forkExtended, bodyExtended, jumpExtended, count, residual⟩

#print axioms generated_while_maximal_condition_branch
end Goose.Lower
