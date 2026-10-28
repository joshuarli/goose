import Goose.Lower.DemandWhileReentry

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_while_reentry_post {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {condition : Expr} {body : Core.Block} {middle : St} (branch : BlockSource cfg env [] body middle)
    {headerState forked bodyStart bodyEnd : LS} {initial conditionFrame finalFrame : GIR.Frame}
    {header exitBlock bodyBlock bodyValue : Nat} {conditionPoint bodyPoint : Pt} {after : St}
    {map required : RetainedSsaMap}
    (headerPoint : headerState.pp = some (header, 0)) (headerRelated : Rel cfg env cx initial headerState)
    (conditionPost : Post cfg env cx headerState initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2 conditionFrame conditionPoint
      [((lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1, .val (.bool true))])
    (forkRun : fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1
      (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2 =
      ((bodyBlock, exitBlock), forked)) (forkExtended : ExtT forked cx.fn.blocks)
    (bodyEq : bodyStart = { forked with cur := some bodyBlock })
    (bodyRun : lowerBlock (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length,
      exitBlock, .jump header⟩) [] false body (lowerEnv cfg.mod env.vars results) bodyStart = (bodyValue, bodyEnd))
    (ended : GeneratedBranchBlockEnd branch map required cx results bodyStart
      (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
      conditionFrame (.normal .unit) ⟨bodyPoint, finalFrame, after⟩) :
    Post cfg env cx headerState initial headerState finalFrame (header, 0) [] := by
  have bodyPost : Post cfg env cx bodyStart conditionFrame bodyEnd finalFrame bodyPoint [] := by
    simpa only [bodyRun] using ended.post
  obtain ⟨_, _, _, valsEq, _, _, _, _, _⟩ := fork_facts forkRun conditionPost.pp forkExtended
  have startVals : bodyStart.vals.size = (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.vals.size := by
    rw [bodyEq]
    exact congrArg Array.size valsEq
  have same := conditionPost.same.trans bodyPost.same (Nat.le_trans conditionPost.mono (Nat.le_of_eq startVals.symm))
  have related : Rel cfg env cx finalFrame headerState := bodyPost.rel.stack_eq (by
    rw [headerRelated.stack, bodyPost.rel.stack])
  exact Post.nil headerPoint (Nat.le_refl _) same related

#print axioms generated_while_reentry_post
end Goose.Lower
