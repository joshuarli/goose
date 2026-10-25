import Goose.Lower.DemandAssignment

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

noncomputable def literalAssignmentRhsContext {cfg : Cfg} {env : Env} {state : St}
    {varId : VarId} {type : IntTy} {number : Int} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.var varId) (.lit type number) origin) state) :
    EvaluationContext cfg.mod source.plans (source.path ++ [1]) (.expression (.lit type number)) .expression :=
  source.context.child rfl 1 (.expression (.lit type number)) .expression
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

theorem literalAssignmentRhsContext.inputFuture {cfg : Cfg} {env : Env} {state : St}
    {varId : VarId} {type : IntTy} {number : Int} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.var varId) (.lit type number) origin) state) :
    (literalAssignmentRhsContext source).inputFuture = source.context.outputFuture := by
  cases contextEq : source.context with
  | pilot profile active =>
    unfold literalAssignmentRhsContext
    rw [contextEq]
    simp [EvaluationContext.child, EvaluationContext.inputFuture, EvaluationContext.outputFuture,
      DemandNode.variables, Expr.variables, DemandNode.visibleForChild, DemandNode.visibleAfter]
  | shrink profile context =>
    let transition := context.child rfl 1 (.expression (.lit type number)) .expression
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have future := DemandNode.childFrame_future transition.childFrameEq
      (show (DemandNode.statement (.assign (.var varId) (.lit type number) origin)).childExpectation?
        _ ⟨source.path, .expression, context.expected.frame.active,
          context.expected.frame.future, context.expected.frame.retained⟩ 1 =
        some ⟨context.expected.frame.active, context.expected.frame.future⟩ from by
        simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children,
          DemandNode.visibleForChild])
    unfold literalAssignmentRhsContext
    rw [contextEq]
    change transition.context.inputFuture = context.outputFuture
    simp only [NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables, Expr.variables,
      List.nil_append]
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, future]
    rfl

private theorem assignment_child_retains {m : Core.Module} {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {varId : VarId} {expr : Expr} {origin : OriginId}
    (context : NodeContext pc path (.statement (.assign (.var varId) expr origin)) .statement)
    {typing : TEnv} {roots : PEnv} (accessMatches : context.AccessMatches typing roots)
    {alias : RetainedAlias}
    (query : roots.access.aliasPlace (path ++ [0]) (.var varId) = .ok [alias]) :
    let transition := context.child rfl 1 (.expression expr) .expression
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    alias ∈ transition.context.expected.frame.retained := by
  let transition := context.child rfl 1 (.expression expr) .expression
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have accessEq : pc.approvals.access = roots.access := by
    change pc.approvals.access = ⟨roots.mod, roots.impl, roots.ctx⟩
    calc
      pc.approvals.access = ⟨pc.approvals.access.mod, pc.approvals.access.impl, pc.approvals.access.ctx⟩ := rfl
      _ = ⟨roots.mod, roots.impl, roots.ctx⟩ := by
        rw [accessMatches.2.2.1, accessMatches.2.2.2.1, accessMatches.2.2.2.2]
  have aliases : (DemandNode.statement (.assign (.var varId) expr origin)).retainedForChild
      pc.approvals.access path 1 = .ok [alias] := by
    simp [DemandNode.retainedForChild, accessEq, query]
  have retained := DemandNode.childFrame_newAlias transition.childFrameEq aliases (alias := alias) (by simp)
  have phased := DemandNode.phaseFrame_retains transition.phaseFrameEq retained
  change alias ∈ transition.context.expected.frame.retained
  rw [transition.expectedFrameEq]
  exact phased

theorem literalAssignmentRhsContext.retains {cfg : Cfg} {env : Env} {state : St}
    {varId : VarId} {type : IntTy} {number : Int} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.var varId) (.lit type number) origin) state)
    (shrink : cfg.mod.profile = .shrink) {alias : RetainedAlias}
    (query : source.rootsEnv.access.aliasPlace (source.path ++ [0]) (.var varId) = .ok [alias]) :
    alias ∈ (literalAssignmentRhsContext source).retained := by
  cases contextEq : source.context with
  | pilot profile active => cases profile.symm.trans shrink
  | shrink profile context =>
    have accessMatches := source.access
    rw [contextEq] at accessMatches
    unfold literalAssignmentRhsContext
    rw [contextEq]
    exact assignment_child_retains context accessMatches query

end Goose.Lower
