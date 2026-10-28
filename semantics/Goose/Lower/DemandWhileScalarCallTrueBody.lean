import Goose.Lower.DemandCallLoopMixedBody
import Goose.Lower.DemandWhileTrueBody

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_scalar_call_true_body {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state middle : St} (source : StmtSource cfg env (.while condition body origin) state)
    (child : ExprSource cfg env condition state)
    (canonical : source.ExpressionChildAt child (by simp [DemandNode.child?, DemandNode.children]))
    {fuel : Nat} (evaluated : evalExpr fuel cfg env condition state = .ok (.bool true) middle)
    (fragment : ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
    (noValue : body.value = none)
    {cx : FnCtx} {results : List Ty} {loop : Option LoopCtx} {root : DemandNode} {owner : Nat}
    (targetConfig : cx.cfg = ⟨cfg.profile, lower cfg.mod⟩)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context) {before headerState built : LS}
    {header : BlockId} {initial frame : GIR.Frame} {point : Pt}
    (headerInput : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv headerState initial (header, 0))
    (headerTarget : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = [])
    (headerId : header = (newBlock [] (lowerEnv cfg.mod env.vars results) before).1.1)
    (headerEq : headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (boundary : ExpressionDemandBoundary child map cx headerState initial
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2
      (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1 (.bool true) middle point frame)
    (conditionReach : Evidence.RuntimePoint cx.cfg cx.fn point frame middle)
    (lowered : lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) headerState = ((), built)) (extended : ExtT built cx.fn.blocks)
    :
    ∃ (bodyBlock exitBlock : BlockId) (forked bodyStart bodyEnd jumped : LS) (value : Nat)
      (branch : BlockSource cfg env [] body middle),
      source.BlockChildAt branch 1 (by simp [DemandNode.child?, DemandNode.children]) ∧
      fork (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).1
        (lowerEnv cfg.mod env.vars results) (lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2 =
        ((bodyBlock, exitBlock), forked) ∧ bodyStart = { forked with cur := some bodyBlock } ∧
      lowerBlock (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length,
        exitBlock, .jump header⟩) [] false body (lowerEnv cfg.mod env.vars results) bodyStart = (value, bodyEnd) ∧
      emitTerm (.br header []) (lowerEnv cfg.mod env.vars results) bodyEnd = ((), jumped) ∧
      ExtT jumped cx.fn.blocks ∧
      (∀ targetFuel, DemandInstructionStep cx targetFuel ⟨point, frame, middle⟩ ⟨(bodyBlock, 0), frame, middle⟩) ∧
      (∀ {taken : Nat} {reached : DemandRuntimePoint},
      DemandRuntimePrefix cx taken ⟨(bodyBlock, 0), frame, middle⟩ reached →
      GeneratedGenericBranchBlockDecomposition branch selected map required bodyStart
        (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
        frame (bodyBlock, 0)
        (@ReachableScalarCallCursor cfg { env with scopes := (body.scope, middle.nextScope) :: env.scopes } cx.fn results
          (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩))
        taken reached) ∧
      (∀ {taken : Nat} {reached : DemandRuntimePoint},
        DemandRuntimePrefix cx taken ⟨(bodyBlock, 0), frame, middle⟩ reached →
        ∀ {targetFuel : Nat} {stop : Stop} {after : St}, DemandInstructionStop cx targetFuel reached stop after →
          stop ≠ .timeout → StoppedLoopBranchBlockPrefix branch map required cx results bodyStart
            (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩)
            frame (bodyBlock, 0) taken reached stop after) := by
  cases cx with
  | mk current caller =>
    change current = ⟨cfg.profile, lower cfg.mod⟩ at targetConfig
    subst current
    obtain ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, value, forkRun, bodyEq, bodyRun,
      jumpRun, finalEq, forkExtended, bodyExtended, jumpExtended, branchStep⟩ :=
      generated_while_test_branch (state := middle) true lowered boundary.post extended
    obtain ⟨branch, typing, roots, canonicalBranch, branchOwner, branchAdmitted, branchBounded, branchRealized,
      branchOccurrence, branchRows, branchInput⟩ :=
      accepted_generated_while_body_ready source child canonical evaluated selected owned headerInput headerTarget headerId headerEq
        occurrence rows admitted boundary forkRun bodyEq forkExtended
    have bodyExt : ExtT (lowerBlock (some ⟨(lowerExpr condition (lowerEnv cfg.mod env.vars results) headerState).2.stack.length, exitBlock, .jump header⟩) [] false body (lowerEnv cfg.mod env.vars results) bodyStart).2 caller.blocks := by
      rw [bodyRun]
      exact bodyExtended
    refine ⟨bodyBlock, exitBlock, forked, bodyStart, bodyEnd, jumped, value, branch, canonicalBranch, forkRun, bodyEq,
      bodyRun, jumpRun, jumpExtended, branchStep, ?_⟩
    have bodyReach : Evidence.RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller (bodyBlock, 0) frame middle := by
      exact Evidence.RuntimePoint.step conditionReach (branchStep 0).runtime
    have agreement := accepted_generated_scalar_call_loop_body branch fragment noValue selected branchOwner branchOccurrence branchRows coverage branchAdmitted branchBounded branchRealized
      branchInput bodyExt bodyReach
    exact agreement

#print axioms accepted_generated_while_scalar_call_true_body
end Goose.Lower
