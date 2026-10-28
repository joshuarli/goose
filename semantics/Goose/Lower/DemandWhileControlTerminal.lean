import Goose.Lower.DemandWhileControlHeader
import Goose.Lower.DemandWhileMaximalBranch

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_control_terminal_branch {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state : St} (source : StmtSource cfg env (.while condition body origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before headerState built : LS} {header : BlockId}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement none (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {frame : GIR.Frame} (realized : map.Realizes cfg.mod source.world env ⟨(header, 0), frame, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv headerState frame (header, 0))
    (headerEq : headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before)
    (coverage : map.Covers required) (bounded : map.Bounded headerState.vals.size)
    (form : ControlPrefixExpression condition)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) headerState = ((), built)) (extended : ExtT built cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨(header, 0), frame, state⟩ reached)
    {term : Term} (terminal : instAt cx.fn reached.point = some (.term term))
    {fuel : Nat} (maximal : ∀ next, ¬ DemandInstructionStep cx fuel reached next) :
    ∃ (child : ExprSource cfg env condition state) (boolean : Bool) (sourceFuel consumed : Nat)
      (boundary : DemandRuntimePoint),
      child.ty = .bool ∧ source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]) ∧
      evalExpr sourceFuel cfg env condition state = .ok (.bool boolean) boundary.state ∧
      DemandRuntimePrefix cx consumed ⟨(header, 0), frame, state⟩ boundary ∧
      GeneratedExpressionPrefixEnd child map cx headerState frame
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1 (.bool boolean) boundary ∧
      ∃ bodyBlock exitBlock forked bodyStart bodyEnd jumped bodyValue remaining,
        consumed + (remaining + 1) = taken ∧
        fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1
          (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2 =
          ((bodyBlock, exitBlock), forked) ∧ bodyStart = { forked with cur := some bodyBlock } ∧
        lowerBlock (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length,
          exitBlock, .jump header⟩) [] false body (lowerEnv cfg.mod env.vars results) bodyStart = (bodyValue, bodyEnd) ∧
        emitTerm (.br header []) (lowerEnv cfg.mod env.vars results) bodyEnd = ((), jumped) ∧
        built = { jumped with cur := some exitBlock } ∧ ExtT forked cx.fn.blocks ∧ ExtT bodyEnd cx.fn.blocks ∧
        ExtT jumped cx.fn.blocks ∧
        DemandRuntimePrefix cx remaining ⟨(if boolean then bodyBlock else exitBlock, 0), boundary.frame, boundary.state⟩ reached := by
  obtain ⟨child, ty, canonical, sourceFuel, consumed, rest, boundary, value, count, traversed, residual, evaluated, post⟩ :=
    accepted_generated_while_control_header_terminal_after_condition source selected owned occurrence rows admitted realized input headerEq
      coverage bounded form lowered extended steps terminal maximal
  have typed := (child.result sourceFuel value evaluated).typed
  rw [ty] at typed
  obtain ⟨boolean, rfl⟩ := hasTy_bool typed
  obtain ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, bodyValue, remaining,
    forkRun, bodyEq, bodyRun, jumpRun, finalEq, forkExtended, bodyExtended, jumpExtended, branchCount, branchResidual⟩ :=
    generated_while_maximal_condition_branch boolean lowered post.post extended residual maximal
  exact ⟨child, boolean, sourceFuel, consumed, boundary, ty, canonical, evaluated, traversed, post,
    bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, bodyValue, remaining, by omega,
    forkRun, bodyEq, bodyRun, jumpRun, finalEq, forkExtended, bodyExtended, jumpExtended, branchResidual⟩

#print axioms accepted_generated_while_control_terminal_branch
end Goose.Lower
