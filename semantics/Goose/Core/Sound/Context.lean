import Goose.Core.Demand

/-!
Checked demand contexts connect one owner's derived plan to source nodes in
the traversal that produced its expected demand points.
-/

namespace Goose.Core.Sound
open Goose.Core

/-- One owner's plan and replay are selected from the same successful derivation. -/
structure PlanContext (m : Module) (plans : Array (Array DemandPoint)) where
  derived : deriveModuleDemand m = .ok plans
  wellFormed : PlansWellFormed m plans
  owner : Nat
  plan : Array DemandPoint
  ownerPlan : plans[owner]? = some plan
  expected : List DemandExpectedPoint
  expectedWalk : DemandNode.expectedPoints m owner = .ok expected
  approvals : DemandPlanApprovals m owner plan expected

/-- Construct an owner context from the exact checked plan array. -/
noncomputable def PlanContext.ofDerived {m : Module} {plans : Array (Array DemandPoint)}
    (derived : deriveModuleDemand m = .ok plans)
    (wellFormed : PlansWellFormed m plans)
    (owner : Nat) (plan : Array DemandPoint) (ownerPlan : plans[owner]? = some plan) :
    PlanContext m plans := by
  let allApprovals := Classical.choose (deriveModuleDemand_ok_approvals m plans derived)
  have selected := allApprovals owner plan ownerPlan
  let ⟨expected, ⟨expectedWalk⟩, approvals⟩ := Classical.choice selected
  exact ⟨derived, wellFormed, owner, plan, ownerPlan, expected, expectedWalk, approvals⟩

/-- A source occurrence with its membership and focus in one plan context. -/
structure NodeContext {m : Module} {plans : Array (Array DemandPoint)}
    (planContext : PlanContext m plans) (path : List Nat) (node : DemandNode)
    (phase : DemandPhase) where
  expected : DemandExpectedPoint
  sourceAt : DemandExpectedSourceAt m planContext.owner path node phase expected
  member : expected ∈ planContext.expected
  focus : DemandExpectedFocus m planContext.plan planContext.owner path phase node expected

def NodeContext.inputFuture {m : Module} {plans : Array (Array DemandPoint)}
    {planContext : PlanContext m plans} {path : List Nat} {node : DemandNode}
    {phase : DemandPhase} (context : NodeContext planContext path node phase) : List VarId :=
  node.variables ++ context.expected.frame.future

def NodeContext.outputFuture {m : Module} {plans : Array (Array DemandPoint)}
    {planContext : PlanContext m plans} {path : List Nat} {node : DemandNode}
    {phase : DemandPhase} (context : NodeContext planContext path node phase) : List VarId :=
  context.expected.frame.future

def NodeContext.ActiveMatches {m : Module} {plans : Array (Array DemandPoint)}
    {planContext : PlanContext m plans} {path : List Nat} {node : DemandNode}
    {phase : DemandPhase} (context : NodeContext planContext path node phase)
    (tenv : TEnv) : Prop :=
  context.expected.toPoint.ActiveMatches tenv.visible

def NodeContext.AccessMatches {m : Module} {plans : Array (Array DemandPoint)}
    {planContext : PlanContext m plans} {path : List Nat} {node : DemandNode}
    {phase : DemandPhase} (_context : NodeContext planContext path node phase)
    (tenv : TEnv) (penv : PEnv) : Prop :=
  planContext.approvals.access.mod = tenv.mod ∧
    planContext.approvals.access.impl.vars = tenv.vars ∧
    planContext.approvals.access.mod = penv.mod ∧
    planContext.approvals.access.impl = penv.impl ∧
    planContext.approvals.access.ctx = penv.ctx

/-- Child frames retain the exact transitions used to select the child focus. -/
structure NodeChildContext {m : Module} {plans : Array (Array DemandPoint)}
    {planContext : PlanContext m plans} {path : List Nat} {node : DemandNode}
    {phase : DemandPhase} (parent : NodeContext planContext path node phase)
    (index : Nat) (child : DemandNode) (childPhase : DemandPhase) where
  context : NodeContext planContext (path ++ [index]) child childPhase
  childFrame : DemandFrame
  childFrameEq : node.childFrame planContext.approvals.access path
    parent.expected.frame index = .ok childFrame
  phaseFrame : DemandFrame
  phaseFrameEq : child.phaseFrame planContext.approvals.access (path ++ [index])
    childFrame childPhase = .ok phaseFrame
  expectedFrameEq : context.expected.frame = phaseFrame

/-- A phase context retains the exact same-node phase transition. -/
structure NodePhaseContext {m : Module} {plans : Array (Array DemandPoint)}
    {planContext : PlanContext m plans} {path : List Nat} {node : DemandNode}
    {phase : DemandPhase} (parent : NodeContext planContext path node phase)
    (targetPhase : DemandPhase) where
  context : NodeContext planContext path node targetPhase
  phaseFrame : DemandFrame
  phaseFrameEq : node.phaseFrame planContext.approvals.access path
    parent.expected.frame targetPhase = .ok phaseFrame
  expectedFrameEq : context.expected.frame = phaseFrame

/-- Source evidence and membership in the plan context produce a focused node. -/
noncomputable def NodeContext.ofSource {m : Module} {plans : Array (Array DemandPoint)}
    (planContext : PlanContext m plans) {path : List Nat} {node : DemandNode}
    {phase : DemandPhase} (expected : DemandExpectedPoint)
    (sourceAt : DemandExpectedSourceAt m planContext.owner path node phase expected)
    (member : expected ∈ planContext.expected) : NodeContext planContext path node phase := by
  have facts := sourceAt.sourceFacts
  exact ⟨expected, sourceAt, member,
    DemandFocus.ofExpectedSource planContext.wellFormed planContext.ownerPlan sourceAt
      facts.1 facts.2⟩

/-- Move to another checked phase of the same node in the same expected walk. -/
noncomputable def NodeContext.phase {m : Module} {plans : Array (Array DemandPoint)}
    {planContext : PlanContext m plans} {path : List Nat} {node : DemandNode}
    {phase : DemandPhase} (parent : NodeContext planContext path node phase)
    (primary : phase = node.primaryPhase) (targetPhase : DemandPhase)
    (hphase : DemandNodeHasPhase node targetPhase) :
    NodePhaseContext parent targetPhase := by
  let phaseFrames := Classical.choice (parent.sourceAt.phaseFrame primary hphase
    planContext.approvals.accessMatches)
  have hpoints : phaseFrames.points = planContext.expected := by
    have hwalk := phaseFrames.walk.symm.trans planContext.expectedWalk
    injection hwalk
  have targetMember : phaseFrames.targetExpected ∈ planContext.expected := by
    simpa only [hpoints] using phaseFrames.targetMember
  let context := NodeContext.ofSource planContext phaseFrames.targetExpected
    phaseFrames.targetSource targetMember
  exact ⟨context, phaseFrames.phaseFrame, phaseFrames.phaseFrameEq,
    phaseFrames.expectedFrameEq⟩

/-- Move to a child using the same owner access environment and expected walk. -/
noncomputable def NodeContext.child {m : Module} {plans : Array (Array DemandPoint)}
    {planContext : PlanContext m plans} {path : List Nat} {node : DemandNode}
    {phase : DemandPhase} (parent : NodeContext planContext path node phase)
    (primary : phase = node.primaryPhase) (index : Nat) (child : DemandNode)
    (childPhase : DemandPhase) (hchild : node.child? index = some child)
    (hchildPhase : DemandNodeHasPhase child childPhase) :
    NodeChildContext parent index child childPhase := by
  let childFrames := Classical.choice (parent.sourceAt.childFrame primary hchild hchildPhase
    planContext.approvals.accessMatches)
  have hpoints : childFrames.points = planContext.expected := by
    have hwalk := childFrames.walk.symm.trans planContext.expectedWalk
    injection hwalk
  have childMember : childFrames.childExpected ∈ planContext.expected := by
    simpa only [hpoints] using childFrames.childMember
  let context := NodeContext.ofSource planContext childFrames.childExpected
    childFrames.childSource childMember
  exact ⟨context, childFrames.childFrame, childFrames.childFrameEq,
    childFrames.phaseFrame, childFrames.phaseFrameEq, childFrames.expectedFrameEq⟩

/-- The recursive constructor preserves list membership and derives both futures. -/
theorem NodeContext.child_keeps_context {m : Module}
    {plans : Array (Array DemandPoint)}
    {planContext : PlanContext m plans} {path : List Nat} {node : DemandNode}
    {phase : DemandPhase} (parent : NodeContext planContext path node phase)
    (primary : phase = node.primaryPhase) (index : Nat) (child : DemandNode)
    (childPhase : DemandPhase) (hchild : node.child? index = some child)
    (hchildPhase : DemandNodeHasPhase child childPhase) :
    ∃ result : NodeChildContext parent index child childPhase,
      result.context.expected ∈ planContext.expected ∧
        node.childFrame planContext.approvals.access path parent.expected.frame index =
          .ok result.childFrame ∧
        child.phaseFrame planContext.approvals.access (path ++ [index]) result.childFrame
          childPhase = .ok result.phaseFrame ∧
        result.context.expected.frame = result.phaseFrame ∧
        result.context.inputFuture = child.variables ++ result.context.outputFuture := by
  let result := NodeContext.child parent primary index child childPhase hchild hchildPhase
  exact ⟨result, result.context.member, result.childFrameEq, result.phaseFrameEq,
    result.expectedFrameEq, rfl⟩

/-- Phase transitions preserve membership and the exact frame used by replay. -/
theorem NodeContext.phase_keeps_context {m : Module}
    {plans : Array (Array DemandPoint)}
    {planContext : PlanContext m plans} {path : List Nat} {node : DemandNode}
    {phase : DemandPhase} (parent : NodeContext planContext path node phase)
    (primary : phase = node.primaryPhase) (targetPhase : DemandPhase)
    (hphase : DemandNodeHasPhase node targetPhase) :
    ∃ result : NodePhaseContext parent targetPhase,
      result.context.expected ∈ planContext.expected ∧
        node.phaseFrame planContext.approvals.access path parent.expected.frame targetPhase =
          .ok result.phaseFrame ∧
        result.context.expected.frame = result.phaseFrame := by
  let result := NodeContext.phase parent primary targetPhase hphase
  exact ⟨result, result.context.member, result.phaseFrameEq, result.expectedFrameEq⟩

end Goose.Core.Sound
