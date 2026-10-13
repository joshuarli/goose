import Goose.Core.Demand
import Goose.Core.Sound.Frame

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
  let rootOccurrence := DemandNode.expectedPoints_root_withFrame planContext.expectedWalk rootAt
  let expected := Classical.choose rootOccurrence
  have occurrenceFacts := Classical.choose_spec rootOccurrence
  have member := occurrenceFacts.1
  have sourceAt := occurrenceFacts.2.1
  exact NodeContext.ofSource planContext expected sourceAt member

/-- A context selected at the owner root has the exact lexical entry frame. -/
theorem NodeContext.atRoot_active {m : Module} {plans : Array (Array DemandPoint)}
    (planContext : PlanContext m plans) (root : DemandNode)
    (rootAt : demandRoot? m planContext.owner = some root) :
    (NodeContext.atRoot planContext root rootAt).expected.frame.active =
      demandInitialActive m planContext.owner := by
  unfold NodeContext.atRoot
  let rootOccurrence := DemandNode.expectedPoints_root_withFrame planContext.expectedWalk rootAt
  have occurrenceFacts := Classical.choose_spec rootOccurrence
  exact congrArg DemandFrame.active occurrenceFacts.2.2

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

/-- Only invalidating approved owners can shrink storage outside this activation. -/
def _root_.Goose.Core.DemandOwner.denotesExternalShrink (P : Nat → RootInst → Prop)
    (owner : DemandOwner) (r : RootInst) : Prop :=
  owner.invalidates = true ∧ Gam noEnv P owner.roots r

/-- Runtime external roots requested by invalidating mutation owners in the checked walk. -/
def PlanMayShrink {m : Module} {plans : Array (Array DemandPoint)}
    (pc : PlanContext m plans) (P : Nat → RootInst → Prop) (r : RootInst) : Prop :=
  ∃ occurrence, occurrence ∈ pc.expected ∧ occurrence.phase = .mutation ∧
    ∃ owner, owner ∈ occurrence.shrinkOwners ∧ owner.denotesExternalShrink P r

/-- Protection covers every invalidating owner requested by the checked walk. -/
theorem PlanMayShrink.ofExpected {m : Module} {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {P : Nat → RootInst → Prop} {r : RootInst}
    {occurrence : DemandExpectedPoint} {owner : DemandOwner}
    (hoccurrence : occurrence ∈ pc.expected) (hphase : occurrence.phase = .mutation)
    (howner : owner ∈ occurrence.shrinkOwners)
    (hdenotes : owner.denotesExternalShrink P r) : PlanMayShrink pc P r := by
  exact ⟨occurrence, hoccurrence, hphase, owner, howner, hdenotes⟩

/-- Pilot uses lexical activity; shrink uses a checked source occurrence. -/
inductive EvaluationContext (m : Module) (plans : Array (Array DemandPoint))
    (path : List Nat) (node : DemandNode) (phase : DemandPhase) : Type
  | pilot (profile : m.profile = .pilot) (active : List VarId)
  | shrink {pc : PlanContext m plans} (profile : m.profile = .shrink)
      (context : NodeContext pc path node phase)

def EvaluationContext.inputFuture {m plans path node phase}
    (context : EvaluationContext m plans path node phase) : List VarId :=
  match context with
  | .pilot _ active => node.variables ++ active
  | .shrink _ context => context.inputFuture

def EvaluationContext.outputFuture {m plans path node phase}
    (context : EvaluationContext m plans path node phase) : List VarId :=
  match context with
  | .pilot _ active => node.visibleAfter active
  | .shrink _ context => context.outputFuture

def EvaluationContext.retained {m plans path node phase}
    (context : EvaluationContext m plans path node phase) : List RetainedAlias :=
  match context with
  | .pilot _ _ => []
  | .shrink _ context => context.expected.frame.retained

def EvaluationContext.ActiveMatches {m plans path node phase}
    (context : EvaluationContext m plans path node phase) (tenv : TEnv) : Prop :=
  match context with
  | .pilot _ active => ∀ x, x ∈ active ↔ x ∈ tenv.visible
  | .shrink _ context => context.ActiveMatches tenv

def EvaluationContext.AccessMatches {m plans path node phase}
    (context : EvaluationContext m plans path node phase) (tenv : TEnv) (penv : PEnv) : Prop :=
  match context with
  | .pilot _ _ => True
  | .shrink _ context => context.AccessMatches tenv penv

def EvaluationContext.OwnerMatches {m plans path node phase}
    (context : EvaluationContext m plans path node phase) (owner : Nat) : Prop :=
  match context with
  | .pilot _ _ => True
  | .shrink (pc := pc) _ _ => pc.owner = owner

def EvaluationContext.mayShrink {m plans path node phase}
    (context : EvaluationContext m plans path node phase)
    (P : Nat → RootInst → Prop) (r : RootInst) : Prop :=
  match context with
  | .pilot _ _ => False
  | .shrink (pc := pc) _ _ => PlanMayShrink pc P r

/-- Re-select a body root from the plan's checked walk. -/
noncomputable def NodeContext.canonicalCallBody {m plans c ctx impl}
    {pc : PlanContext m plans}
    (_context : NodeContext pc [] (.block impl.body) .block)
    (ownerMatch : pc.owner = c)
    (hctx : m.contexts[c]? = some ctx)
    (himpl : m.impls[ctx.impl]? = some impl) :
    NodeContext pc [] (.block impl.body) .block := by
  have hrootAt : demandRoot? m pc.owner = some (.block impl.body) := by
    rw [ownerMatch]
    exact demandRoot?_context hctx himpl
  exact NodeContext.atRoot pc (.block impl.body) hrootAt

/-- The re-selected body context has precisely the implementation parameters active. -/
theorem NodeContext.canonicalCallBody_active {m plans c ctx impl}
    {pc : PlanContext m plans}
    (context : NodeContext pc [] (.block impl.body) .block)
    (ownerMatch : pc.owner = c)
    (hctx : m.contexts[c]? = some ctx)
    (himpl : m.impls[ctx.impl]? = some impl) :
    (context.canonicalCallBody ownerMatch hctx himpl).expected.frame.active =
      impl.params.toList.map (·.var) := by
  have hrootAt : demandRoot? m pc.owner = some (.block impl.body) := by
    rw [ownerMatch]
    exact demandRoot?_context hctx himpl
  change (NodeContext.atRoot pc (.block impl.body) hrootAt).expected.frame.active = _
  rw [NodeContext.atRoot_active]
  rw [ownerMatch]
  have ⟨hc, hctxValue⟩ := Array.getElem?_eq_some_iff.mp hctx
  simp [demandInitialActive, hc, hctxValue, himpl]

/-- Re-selecting the root does not change the exact access environment. -/
theorem NodeContext.canonicalCallBody_accessMatches {m plans c ctx impl}
    {pc : PlanContext m plans}
    (context : NodeContext pc [] (.block impl.body) .block)
    (ownerMatch : pc.owner = c)
    (hctx : m.contexts[c]? = some ctx)
    (himpl : m.impls[ctx.impl]? = some impl)
    (tenv : TEnv) (penv : PEnv)
    (htmod : tenv.mod = m) (htvars : tenv.vars = impl.vars)
    (hpmod : penv.mod = m) (hpimpl : penv.impl = impl) (hpctx : penv.ctx = ctx) :
    (context.canonicalCallBody ownerMatch hctx himpl).AccessMatches tenv penv := by
  have haccessPlan : demandAccess? m c = some pc.approvals.access := by
    simpa [ownerMatch] using pc.approvals.accessMatches
  have haccessContext := demandAccess?_context hctx himpl
  have haccessEq : pc.approvals.access = ⟨m, impl, ctx⟩ :=
    Option.some.inj (haccessPlan.symm.trans haccessContext)
  change pc.approvals.access.mod = tenv.mod ∧
    pc.approvals.access.impl.vars = tenv.vars ∧
    pc.approvals.access.mod = penv.mod ∧
    pc.approvals.access.impl = penv.impl ∧
    pc.approvals.access.ctx = penv.ctx
  rw [haccessEq]
  exact ⟨htmod.symm, htvars.symm, hpmod.symm, hpimpl.symm, hpctx.symm⟩

/-- Canonical context at a callee body entry, independent of the supplied root occurrence. -/
noncomputable def EvaluationContext.callBody {m plans c ctx impl}
    (root : EvaluationContext m plans [] (.block impl.body) .block)
    (ownerMatch : root.OwnerMatches c)
    (hctx : m.contexts[c]? = some ctx)
    (himpl : m.impls[ctx.impl]? = some impl) :
    EvaluationContext m plans [] (.block impl.body) .block := by
  cases root with
  | pilot profile _ =>
    exact .pilot profile (impl.params.toList.map (·.var))
  | shrink profile context =>
    exact .shrink profile (context.canonicalCallBody ownerMatch hctx himpl)

/-- Canonicalizing a call body preserves its checked shrink authority. -/
theorem EvaluationContext.callBody_mayShrink_iff {m plans c ctx impl}
    (root : EvaluationContext m plans [] (.block impl.body) .block)
    (ownerMatch : root.OwnerMatches c)
    (hctx : m.contexts[c]? = some ctx)
    (himpl : m.impls[ctx.impl]? = some impl)
    (P : Nat → RootInst → Prop) (r : RootInst) :
    (root.callBody ownerMatch hctx himpl).mayShrink P r ↔ root.mayShrink P r := by
  cases root <;> simp [EvaluationContext.callBody, EvaluationContext.mayShrink,
    NodeContext.canonicalCallBody]

/-- The canonical call body is active exactly on the implementation parameters. -/
theorem EvaluationContext.callBody_activeMatches {m plans c ctx impl}
    (root : EvaluationContext m plans [] (.block impl.body) .block)
    (ownerMatch : root.OwnerMatches c)
    (hctx : m.contexts[c]? = some ctx)
    (himpl : m.impls[ctx.impl]? = some impl)
    (tenv : TEnv)
    (hvisible : ∀ x, x ∈ tenv.visible ↔ x ∈ impl.params.toList.map (·.var)) :
    (root.callBody ownerMatch hctx himpl).ActiveMatches tenv := by
  cases root with
  | pilot profile _ =>
    change ∀ x, x ∈ impl.params.toList.map (·.var) ↔ x ∈ tenv.visible
    intro x
    exact (hvisible x).symm
  | shrink profile context =>
    let canonical := context.canonicalCallBody ownerMatch hctx himpl
    have hactive := NodeContext.canonicalCallBody_active context ownerMatch hctx himpl
    change canonical.ActiveMatches tenv
    change ∀ x, x ∈ canonical.expected.frame.active ↔ x ∈ tenv.visible
    intro x
    rw [hactive]
    exact (hvisible x).symm

/-- Access checks at the canonical call body use the looked up context and implementation. -/
theorem EvaluationContext.callBody_accessMatches {m plans c ctx impl}
    (root : EvaluationContext m plans [] (.block impl.body) .block)
    (ownerMatch : root.OwnerMatches c)
    (hctx : m.contexts[c]? = some ctx)
    (himpl : m.impls[ctx.impl]? = some impl)
    (tenv : TEnv) (penv : PEnv)
    (htmod : tenv.mod = m) (htvars : tenv.vars = impl.vars)
    (hpmod : penv.mod = m) (hpimpl : penv.impl = impl) (hpctx : penv.ctx = ctx) :
    (root.callBody ownerMatch hctx himpl).AccessMatches tenv penv := by
  cases root with
  | pilot profile _ => simp [EvaluationContext.callBody, EvaluationContext.AccessMatches]
  | shrink profile context =>
    exact NodeContext.canonicalCallBody_accessMatches context ownerMatch hctx himpl
      tenv penv htmod htvars hpmod hpimpl hpctx

/-- Children keep lexical activity or follow the checked child transition. -/
noncomputable def EvaluationContext.child {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (index : Nat) (child : DemandNode)
    (childPhase : DemandPhase) (hchild : node.child? index = some child)
    (hchildPhase : DemandNodeHasPhase child childPhase) :
    EvaluationContext m plans (path ++ [index]) child childPhase :=
  match parent with
  | .pilot profile active => .pilot profile (node.visibleForChild active index)
  | .shrink profile context =>
    .shrink profile (context.child primary index child childPhase hchild hchildPhase).context

/-- Same-node phases preserve pilot activity and use checked shrink transitions. -/
noncomputable def EvaluationContext.phase {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (targetPhase : DemandPhase)
    (hphase : DemandNodeHasPhase node targetPhase) :
    EvaluationContext m plans path node targetPhase :=
  match parent with
  | .pilot profile active => .pilot profile active
  | .shrink profile context => .shrink profile (context.phase primary targetPhase hphase).context

theorem EvaluationContext.child_inputFuture {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (index : Nat) (child : DemandNode)
    (childPhase : DemandPhase) (hchild : node.child? index = some child)
    (hchildPhase : DemandNodeHasPhase child childPhase) :
    (parent.child primary index child childPhase hchild hchildPhase).inputFuture =
      match parent with
      | .pilot _ active => child.variables ++ node.visibleForChild active index
      | .shrink _ context =>
        child.variables ++
          (context.child primary index child childPhase hchild hchildPhase).childFrame.future := by
  cases parent with
  | pilot profile active => rfl
  | shrink profile context =>
    let transition := context.child primary index child childPhase hchild hchildPhase
    change child.variables ++ transition.context.expected.frame.future =
      child.variables ++ transition.childFrame.future
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]

theorem EvaluationContext.child_outputFuture {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (index : Nat) (child : DemandNode)
    (childPhase : DemandPhase) (hchild : node.child? index = some child)
    (hchildPhase : DemandNodeHasPhase child childPhase) :
    (parent.child primary index child childPhase hchild hchildPhase).outputFuture =
      match parent with
      | .pilot _ active => child.visibleAfter (node.visibleForChild active index)
      | .shrink _ context =>
        (context.child primary index child childPhase hchild hchildPhase).childFrame.future := by
  cases parent with
  | pilot profile active => rfl
  | shrink profile context =>
    let transition := context.child primary index child childPhase hchild hchildPhase
    change transition.context.expected.frame.future = transition.childFrame.future
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]

theorem EvaluationContext.phase_inputFuture {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (targetPhase : DemandPhase)
    (hphase : DemandNodeHasPhase node targetPhase) :
    (parent.phase primary targetPhase hphase).inputFuture = parent.inputFuture := by
  cases parent with
  | pilot profile active => rfl
  | shrink profile context =>
    let transition := context.phase primary targetPhase hphase
    change node.variables ++ transition.context.expected.frame.future =
      node.variables ++ context.expected.frame.future
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]

theorem EvaluationContext.phase_outputFuture {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (targetPhase : DemandPhase)
    (hphase : DemandNodeHasPhase node targetPhase) :
    (parent.phase primary targetPhase hphase).outputFuture = parent.outputFuture := by
  cases parent with
  | pilot profile active => rfl
  | shrink profile context =>
    let transition := context.phase primary targetPhase hphase
    change transition.context.expected.frame.future = context.expected.frame.future
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]

theorem EvaluationContext.child_accessMatches_iff {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (index : Nat) (child : DemandNode)
    (childPhase : DemandPhase) (hchild : node.child? index = some child)
    (hchildPhase : DemandNodeHasPhase child childPhase) (tenv : TEnv) (penv : PEnv) :
    (parent.child primary index child childPhase hchild hchildPhase).AccessMatches tenv penv ↔
      parent.AccessMatches tenv penv := by
  cases parent <;> rfl

theorem EvaluationContext.phase_accessMatches_iff {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (targetPhase : DemandPhase)
    (hphase : DemandNodeHasPhase node targetPhase) (tenv : TEnv) (penv : PEnv) :
    (parent.phase primary targetPhase hphase).AccessMatches tenv penv ↔
      parent.AccessMatches tenv penv := by
  cases parent <;> rfl

theorem EvaluationContext.child_mayShrink_iff {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (index : Nat) (child : DemandNode)
    (childPhase : DemandPhase) (hchild : node.child? index = some child)
    (hchildPhase : DemandNodeHasPhase child childPhase) (P : Nat → RootInst → Prop) (r : RootInst) :
    (parent.child primary index child childPhase hchild hchildPhase).mayShrink P r ↔
      parent.mayShrink P r := by
  cases parent <;> rfl

theorem EvaluationContext.phase_mayShrink_iff {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (targetPhase : DemandPhase)
    (hphase : DemandNodeHasPhase node targetPhase) (P : Nat → RootInst → Prop) (r : RootInst) :
    (parent.phase primary targetPhase hphase).mayShrink P r ↔ parent.mayShrink P r := by
  cases parent <;> rfl

theorem EvaluationContext.child_retained_subset {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (index : Nat) (child : DemandNode)
    (childPhase : DemandPhase) (hchild : node.child? index = some child)
    (hchildPhase : DemandNodeHasPhase child childPhase) {alias : RetainedAlias}
    (hmem : alias ∈ parent.retained) :
    alias ∈ (parent.child primary index child childPhase hchild hchildPhase).retained := by
  cases parent with
  | pilot profile active => simp [EvaluationContext.retained] at hmem ⊢
  | shrink profile context =>
    let transition := context.child primary index child childPhase hchild hchildPhase
    change alias ∈ transition.context.expected.frame.retained
    have hchildRetained := DemandNode.childFrame_retains transition.childFrameEq hmem
    have hphaseRetained := DemandNode.phaseFrame_retains transition.phaseFrameEq hchildRetained
    rw [transition.expectedFrameEq]
    exact hphaseRetained

theorem EvaluationContext.phase_retained_subset {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (targetPhase : DemandPhase)
    (hphase : DemandNodeHasPhase node targetPhase) {alias : RetainedAlias}
    (hmem : alias ∈ parent.retained) :
    alias ∈ (parent.phase primary targetPhase hphase).retained := by
  cases parent with
  | pilot profile active => simp [EvaluationContext.retained] at hmem ⊢
  | shrink profile context =>
    let transition := context.phase primary targetPhase hphase
    change alias ∈ transition.context.expected.frame.retained
    have hretained := DemandNode.phaseFrame_retains transition.phaseFrameEq hmem
    rw [transition.expectedFrameEq]
    exact hretained

theorem EvaluationContext.phase_activeMatches {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (targetPhase : DemandPhase)
    (hphase : DemandNodeHasPhase node targetPhase) (tenv : TEnv)
    (hactive : parent.ActiveMatches tenv) :
    (parent.phase primary targetPhase hphase).ActiveMatches tenv := by
  cases parent with
  | pilot profile active => exact hactive
  | shrink profile context =>
    let transition := context.phase primary targetPhase hphase
    change transition.context.expected.toPoint.ActiveMatches tenv.visible
    intro x
    have hpoint : transition.context.expected.toPoint.active =
        transition.phaseFrame.active := by
      rw [DemandExpectedPoint.toPoint]
      rw [transition.expectedFrameEq]
    rw [hpoint, DemandNode.phaseFrame_active transition.phaseFrameEq]
    exact hactive x

theorem EvaluationContext.child_activeMatches {m plans path node phase}
    (parent : EvaluationContext m plans path node phase)
    (primary : phase = node.primaryPhase) (index : Nat) (child : DemandNode)
    (childPhase : DemandPhase) (hchild : node.child? index = some child)
    (hchildPhase : DemandNodeHasPhase child childPhase) (tenv tenv' : TEnv)
    (hactive : parent.ActiveMatches tenv)
    (hvisible : ∀ x, x ∈ tenv'.visible ↔
      x ∈ node.visibleForChild tenv.visible index) :
    (parent.child primary index child childPhase hchild hchildPhase).ActiveMatches tenv' := by
  cases parent with
  | pilot profile active =>
    change ∀ x, x ∈ node.visibleForChild active index ↔ x ∈ tenv'.visible
    intro x
    exact (node.visibleForChild_mem_congr index hactive x).trans (hvisible x).symm
  | shrink profile context =>
    let transition := context.child primary index child childPhase hchild hchildPhase
    change transition.context.expected.toPoint.ActiveMatches tenv'.visible
    intro x
    have hpoint : transition.context.expected.toPoint.active =
        transition.phaseFrame.active := by
      rw [DemandExpectedPoint.toPoint]
      rw [transition.expectedFrameEq]
    rw [hpoint, DemandNode.phaseFrame_active transition.phaseFrameEq,
      DemandNode.childFrame_active transition.childFrameEq]
    exact (node.visibleForChild_mem_congr index hactive x).trans (hvisible x).symm

/-- Select the implementation body with its exact source-node index. -/
noncomputable def ContextPlanSelection.bodyContext {m : Module}
    {plans : Array (Array DemandPoint)} {c : ContextId} {ctx : Context}
    (selection : ContextPlanSelection m plans c ctx) :
    NodeContext selection.planContext [] (.block selection.implementation.body)
      (DemandNode.block selection.implementation.body).primaryPhase := by
  have context := selection.rootContext
  rw [selection.rootNode] at context
  exact context

/-- Select the initializer with its exact source-node index. -/
noncomputable def GlobalPlanSelection.initializerContext {m : Module}
    {plans : Array (Array DemandPoint)} {g : GlobalId} {global : Global}
    (selection : GlobalPlanSelection m plans g global) :
    NodeContext selection.planContext [] (.expression global.init)
      (DemandNode.expression global.init).primaryPhase := by
  have context := selection.rootContext
  rw [selection.rootNode] at context
  exact context

/-- Start a body in either profile from the module's successful demand derivation. -/
noncomputable def EvaluationContext.forContext {m : Module}
    {plans : Array (Array DemandPoint)}
    (derived : deriveModuleDemand m = .ok plans) (wellFormed : PlansWellFormed m plans)
    {c : ContextId} {ctx : Context} (contextAt : m.contexts[c]? = some ctx)
    (implementation : Impl) (implementationAt : m.impls[ctx.impl]? = some implementation) :
    EvaluationContext m plans [] (.block implementation.body)
      (DemandNode.block implementation.body).primaryPhase :=
  match profile : m.profile with
  | .pilot => .pilot profile (implementation.params.toList.map (·.var))
  | .shrink => by
    have notPilot : m.profile ≠ .pilot := by simp [profile]
    let selection := PlanContext.forContext derived wellFormed notPilot contextAt
      implementation implementationAt
    exact .shrink profile selection.bodyContext

/-- Start a global initializer in either profile from the checked derivation. -/
noncomputable def EvaluationContext.forGlobal {m : Module}
    {plans : Array (Array DemandPoint)}
    (derived : deriveModuleDemand m = .ok plans) (wellFormed : PlansWellFormed m plans)
    {g : GlobalId} {global : Global} (globalAt : m.globals[g]? = some global) :
    EvaluationContext m plans [] (.expression global.init)
      (DemandNode.expression global.init).primaryPhase :=
  match profile : m.profile with
  | .pilot => .pilot profile []
  | .shrink => by
    have notPilot : m.profile ≠ .pilot := by simp [profile]
    let selection := PlanContext.forGlobal derived wellFormed notPilot globalAt
    exact .shrink profile selection.initializerContext

/-- Context roots select the plan owner belonging to the looked-up context. -/
theorem EvaluationContext.forContext_ownerMatches {m : Module}
    {plans : Array (Array DemandPoint)}
    (derived : deriveModuleDemand m = .ok plans) (wellFormed : PlansWellFormed m plans)
    {c : ContextId} {ctx : Context} (contextAt : m.contexts[c]? = some ctx)
    (implementation : Impl) (implementationAt : m.impls[ctx.impl]? = some implementation) :
    (EvaluationContext.forContext derived wellFormed contextAt implementation implementationAt).OwnerMatches c := by
  unfold EvaluationContext.forContext
  split
  · trivial
  · rename_i profile
    exact (PlanContext.forContext derived wellFormed (by simp [profile]) contextAt
      implementation implementationAt).ownerEq

/-- Initializer roots select the global's owner after the context owners. -/
theorem EvaluationContext.forGlobal_ownerMatches {m : Module}
    {plans : Array (Array DemandPoint)}
    (derived : deriveModuleDemand m = .ok plans) (wellFormed : PlansWellFormed m plans)
    {g : GlobalId} {global : Global} (globalAt : m.globals[g]? = some global) :
    (EvaluationContext.forGlobal derived wellFormed globalAt).OwnerMatches (m.contexts.size + g) := by
  unfold EvaluationContext.forGlobal
  split
  · trivial
  · rename_i profile
    exact (PlanContext.forGlobal derived wellFormed (by simp [profile]) globalAt).ownerEq

end Goose.Core.Sound
