import Goose.Lower.DemandWhileTest
import Goose.Lower.DemandRunAtPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem generated_while_test_branch_reachable {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {header : BlockId} {before after : LS} {condition : Expr} {body : Core.Block}
    {initial frame : GIR.Frame} {point : Pt} {state : St} (value : Bool)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) before = ((), after))
    (post : Post cfg env cx before initial (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1, .val (.bool value))])
    (extended : ExtT after cx.fn.blocks) (entry : RuntimePoint cx.cfg cx.fn point frame state) :
    ∃ bodyBlock exitBlock forked bodyStart bodyEnd jumped bodyValue,
      fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 (lowerEnv cfg.mod env.vars results)
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2 = ((bodyBlock, exitBlock), forked) ∧
      bodyStart = { forked with cur := some bodyBlock } ∧
      lowerBlock (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2.stack.length, exitBlock, .jump header⟩)
        [] false body (lowerEnv cfg.mod env.vars results) bodyStart = (bodyValue, bodyEnd) ∧
      emitTerm (.br header []) (lowerEnv cfg.mod env.vars results) bodyEnd = ((), jumped) ∧
      after = { jumped with cur := some exitBlock } ∧ ExtT forked cx.fn.blocks ∧
      ExtT bodyEnd cx.fn.blocks ∧ ExtT jumped cx.fn.blocks ∧
      (∀ fuel, DemandInstructionStep cx fuel ⟨point, frame, state⟩
        ⟨(if value then bodyBlock else exitBlock, 0), frame, state⟩) ∧
      RuntimePoint cx.cfg cx.fn (if value then bodyBlock else exitBlock, 0) frame state := by
  obtain ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, bodyValue,
    forkRun, bodyEq, bodyRun, jumpRun, finalEq, forkExtended, bodyExtended, jumpExtended, branch⟩ :=
    generated_while_test_branch value lowered post extended
  exact ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, bodyValue, forkRun, bodyEq, bodyRun, jumpRun,
    finalEq, forkExtended, bodyExtended, jumpExtended, branch, RuntimePoint.step entry (branch 0).runtime⟩

#print axioms generated_while_test_branch_reachable
end Goose.Lower
