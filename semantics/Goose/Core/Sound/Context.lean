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

private theorem PlanContext.ownerPlanExists {m : Module}
    {plans : Array (Array DemandPoint)}
    (wellFormed : PlansWellFormed m plans) (notPilot : m.profile ≠ .pilot)
    {owner : Nat} (ownerLt : owner < m.contexts.size + m.globals.size) :
    ∃ plan, plans[owner]? = some plan := by
  have hprofile : (m.profile == .pilot) = false := by
    cases hprofile : m.profile with
    | pilot => exact False.elim (notPilot hprofile)
    | shrink => rfl
  have hsize : plans.size = m.contexts.size + m.globals.size := by
    simpa [hprofile] using wellFormed.1
  have hownerLt : owner < plans.size := by
    rw [hsize]
    exact ownerLt
  refine ⟨plans[owner]'hownerLt, ?_⟩
  exact Array.getElem?_eq_some_iff.mpr ⟨hownerLt, rfl⟩

/-- A checked context owner paired with its implementation body root and plan. -/
structure ContextPlanSelection (m : Module) (plans : Array (Array DemandPoint))
    (c : ContextId) (ctx : Context) where
  contextAt : m.contexts[c]? = some ctx
  implementation : Impl
  implementationAt : m.impls[ctx.impl]? = some implementation
  planContext : PlanContext m plans
  ownerEq : planContext.owner = c
  root : DemandNode
  rootAt : demandRoot? m c = some root
  rootNode : root = .block implementation.body

/-- A checked global owner paired with its initializer root and plan. -/
structure GlobalPlanSelection (m : Module) (plans : Array (Array DemandPoint))
    (g : GlobalId) (global : Global) where
  globalAt : m.globals[g]? = some global
  planContext : PlanContext m plans
  ownerEq : planContext.owner = m.contexts.size + g
  root : DemandNode
  rootAt : demandRoot? m (m.contexts.size + g) = some root
  rootNode : root = .expression global.init

/-- Select the body plan belonging to a valid context in a non-pilot module. -/
noncomputable def PlanContext.forContext {m : Module} {plans : Array (Array DemandPoint)}
    (derived : deriveModuleDemand m = .ok plans) (wellFormed : PlansWellFormed m plans)
    (notPilot : m.profile ≠ .pilot) {c : ContextId} {ctx : Context}
    (contextAt : m.contexts[c]? = some ctx) (implementation : Impl)
    (implementationAt : m.impls[ctx.impl]? = some implementation) :
    ContextPlanSelection m plans c ctx := by
  have contextLt : c < m.contexts.size := (Array.getElem?_eq_some_iff.mp contextAt).1
  have ownerLt : c < m.contexts.size + m.globals.size :=
    Nat.lt_of_lt_of_le contextLt (Nat.le_add_right _ _)
  let ownerPlanExists := PlanContext.ownerPlanExists wellFormed notPilot ownerLt
  let plan := Classical.choose ownerPlanExists
  have ownerPlan := Classical.choose_spec ownerPlanExists
  let selected := PlanContext.ofDerived derived wellFormed c plan ownerPlan
  have rootAt : demandRoot? m c = some (.block implementation.body) := by
    rw [demandRoot?, if_pos contextLt, contextAt]
    simp only [Option.bind_some]
    rw [implementationAt]
    rfl
  exact ⟨contextAt, implementation, implementationAt, selected, rfl,
    .block implementation.body, rootAt, rfl⟩

/-- Select the initializer plan belonging to a valid global in a non-pilot module. -/
noncomputable def PlanContext.forGlobal {m : Module} {plans : Array (Array DemandPoint)}
    (derived : deriveModuleDemand m = .ok plans) (wellFormed : PlansWellFormed m plans)
    (notPilot : m.profile ≠ .pilot) {g : GlobalId} {global : Global}
    (globalAt : m.globals[g]? = some global) : GlobalPlanSelection m plans g global := by
  have globalLt : g < m.globals.size := (Array.getElem?_eq_some_iff.mp globalAt).1
  have ownerLt : m.contexts.size + g < m.contexts.size + m.globals.size :=
    Nat.add_lt_add_left globalLt m.contexts.size
  let ownerPlanExists := PlanContext.ownerPlanExists wellFormed notPilot ownerLt
  let plan := Classical.choose ownerPlanExists
  have ownerPlan := Classical.choose_spec ownerPlanExists
  let selected := PlanContext.ofDerived derived wellFormed (m.contexts.size + g) plan ownerPlan
  have rootAt : demandRoot? m (m.contexts.size + g) =
      some (.expression global.init) := by
    simp [demandRoot?, globalAt, Nat.not_lt_of_ge (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
  exact ⟨globalAt, selected, rfl, .expression global.init, rootAt, rfl⟩

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

/-- Start replay at an owner's root using its already selected expected walk. -/
noncomputable def NodeContext.atRoot {m : Module} {plans : Array (Array DemandPoint)}
    (planContext : PlanContext m plans) (root : DemandNode)
    (rootAt : demandRoot? m planContext.owner = some root) :
    NodeContext planContext [] root root.primaryPhase := by
  let rootOccurrence := DemandNode.expectedPoints_root planContext.expectedWalk rootAt
  let expected := Classical.choose rootOccurrence
  have occurrenceFacts := Classical.choose_spec rootOccurrence
  have member := occurrenceFacts.1
  have sourceAt := occurrenceFacts.2
  exact NodeContext.ofSource planContext expected sourceAt member

/-- Start at a context body root without rebuilding its demand walk. -/
noncomputable def ContextPlanSelection.rootContext {m : Module}
    {plans : Array (Array DemandPoint)} {c : ContextId} {ctx : Context}
    (selection : ContextPlanSelection m plans c ctx) :
    NodeContext selection.planContext [] selection.root selection.root.primaryPhase := by
  have rootAt : demandRoot? m selection.planContext.owner = some selection.root := by
    rw [selection.ownerEq]
    exact selection.rootAt
  exact NodeContext.atRoot selection.planContext selection.root rootAt

/-- Start at a global initializer root without rebuilding its demand walk. -/
noncomputable def GlobalPlanSelection.rootContext {m : Module}
    {plans : Array (Array DemandPoint)} {g : GlobalId} {global : Global}
    (selection : GlobalPlanSelection m plans g global) :
    NodeContext selection.planContext [] selection.root selection.root.primaryPhase := by
  have rootAt : demandRoot? m selection.planContext.owner = some selection.root := by
    rw [selection.ownerEq]
    exact selection.rootAt
  exact NodeContext.atRoot selection.planContext selection.root rootAt

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
