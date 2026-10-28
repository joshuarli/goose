import Goose.Lower.DemandExpressionCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem expressionChildFuture_includes {expression : Expr} {access : AccessEnv} {parent : DemandPoint}
    {index : Nat} {future : List VarId}
    (actual : (DemandNode.expression expression).childFuture access parent index = some future) :
    ∀ slot, slot ∈ parent.future → slot ∈ future := by
  cases expression <;> simp only [DemandNode.childFuture] at actual
  all_goals repeat' split at actual
  all_goals simp_all [List.mem_append]
  all_goals intro slot member
  all_goals rw [← actual]
  all_goals simp [member]

theorem expressionContext_childOutput_includes {m : Core.Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {expression child : Expr} {index : Nat}
    (context : EvaluationContext m plans path (.expression expression) .expression)
    (found : (DemandNode.expression expression).child? index = some (.expression child)) :
    ∀ slot, slot ∈ context.outputFuture →
      slot ∈ (context.child rfl index (.expression child) .expression found (by trivial)).outputFuture := by
  intro slot member
  have childOutput := EvaluationContext.child_outputFuture context rfl index (.expression child) .expression found (by trivial)
  rw [childOutput]
  cases context with
  | pilot profile active =>
    simpa [EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild] using member
  | @shrink pc profile context =>
    let parent : DemandPoint := ⟨path, .expression, context.expected.frame.active,
      context.expected.frame.future, context.expected.frame.retained⟩
    let transition := context.child rfl index (.expression child) .expression found (by trivial)
    cases futureEq : (DemandNode.expression expression).childFuture pc.approvals.access parent index with
    | none =>
      have impossible := transition.childFrameEq
      simp [DemandNode.childFrame, DemandNode.childExpectation?, parent, found, futureEq, reject] at impossible
    | some future =>
      have expectation : (DemandNode.expression expression).childExpectation? pc.approvals.access parent index =
          some ⟨(DemandNode.expression expression).visibleForChild parent.active index, future⟩ := by
        simp [DemandNode.childExpectation?, found, futureEq]
      have result := DemandNode.childFrame_future transition.childFrameEq expectation
      have included := expressionChildFuture_includes futureEq slot member
      change slot ∈ transition.childFrame.future
      rw [result]
      exact included

theorem expressionContext_input_includes_output {m : Core.Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {expression : Expr}
    (context : EvaluationContext m plans path (.expression expression) .expression)
    {slot : VarId} (member : slot ∈ context.outputFuture) : slot ∈ context.inputFuture := by
  cases context with
  | pilot profile active =>
    simp only [EvaluationContext.outputFuture, DemandNode.visibleAfter] at member
    simp [EvaluationContext.inputFuture, member]
  | shrink profile context =>
    simp only [EvaluationContext.outputFuture, NodeContext.outputFuture] at member
    simp [EvaluationContext.inputFuture, NodeContext.inputFuture, member]

theorem demandContextOutputFutureEq {module : Core.Module}
    {firstPlans secondPlans : Array (Array DemandPoint)} {firstPath secondPath : List Nat}
    {firstNode secondNode : DemandNode} {phase : DemandPhase}
    {first : EvaluationContext module firstPlans firstPath firstNode phase}
    {second : EvaluationContext module secondPlans secondPath secondNode phase}
    (plans : firstPlans = secondPlans) (path : firstPath = secondPath) (node : firstNode = secondNode)
    (same : HEq first second) : first.outputFuture = second.outputFuture := by
  subst secondPlans
  subst secondPath
  subst secondNode
  exact congrArg EvaluationContext.outputFuture (eq_of_heq same)

def ExpressionFutureFrame (cfg : Cfg) (world : World) (typing : TEnv) (roots : PEnv)
    (env : Env) (point : DemandRuntimePoint) (slot : VarId) : Prop :=
  ∃ future : List VarId,
    slot ∈ future ∧ Core.Sound.Frame cfg.mod world typing roots env point.state future

theorem CanonicalExpressionDemand.futureFrame {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    {source : ExprSource cfg env expression state} {map : RetainedSsaMap} {cx : FnCtx}
    {runtime : DemandRuntimePoint} (cursor : CanonicalExpressionDemand map cx source runtime)
    {slot : VarId} (member : slot ∈ source.context.outputFuture) :
    ExpressionFutureFrame cfg source.world source.typingEnv source.rootsEnv env runtime slot := by
  induction cursor with
  | entry demanded =>
    exact ⟨_, expressionContext_input_includes_output _ member, demanded.source⟩
  | exit demanded => exact ⟨_, member, demanded.source⟩
  | @child expression childExpression state childState source child index found runtime metadata demanded induction =>
    have needed : slot ∈ (source.context.child rfl index (.expression childExpression) .expression found (by trivial)).outputFuture :=
      expressionContext_childOutput_includes source.context found slot member
    have childNeeded : slot ∈ child.context.outputFuture := by
      have equality := demandContextOutputFutureEq metadata.plans metadata.path rfl metadata.context
      rw [equality]
      exact needed
    simpa only [metadata.world, metadata.typing, metadata.roots] using induction childNeeded

#print axioms CanonicalExpressionDemand.futureFrame

#print axioms expressionContext_childOutput_includes

#print axioms expressionChildFuture_includes
end Goose.Lower
