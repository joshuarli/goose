import Goose.Core.Sound.Module

namespace Goose.Core

inductive DemandRootSeparate : RootRef → RootRef → Prop
  | locals {x y} : x ≠ y → DemandRootSeparate (.local x) (.local y)
  | globals {x y} : x ≠ y → DemandRootSeparate (.global x) (.global y)
  | localGlobal {x y} : DemandRootSeparate (.local x) (.global y)
  | globalLocal {x y} : DemandRootSeparate (.global x) (.local y)
  | localParam {x y} : DemandRootSeparate (.local x) (.param y)
  | paramLocal {x y} : DemandRootSeparate (.param x) (.local y)

def DemandRootSetsSeparate (owners aliases : List RootRef) : Prop :=
  ∀ owner, owner ∈ owners → ∀ alias, alias ∈ aliases → DemandRootSeparate owner alias

def DemandInterior : Ty → Prop
  | .slice _ _ => True
  | .ref _ target => target.ownerElem? = none
  | _ => False

def DemandInvalidatingOwner : Option Ty → Prop
  | none | some (.grow _) | some (.growshrink _) => True
  | _ => False

def DemandAliasProtected (owner : DemandOwner) (alias : RetainedAlias) : Prop :=
  DemandInvalidatingOwner owner.ty → DemandInterior alias.ty →
    DemandRootSetsSeparate owner.roots alias.roots

structure DeclarativeFrameDemand (access : AccessEnv) (point : DemandPoint)
    (owner : DemandOwner) : Prop where
  variableRoots : ∀ x, x ∈ point.future → x ∈ point.active →
    ∃ aliases, access.aliasVariable x = .ok aliases
  variables : ∀ x, x ∈ point.future → x ∈ point.active → ∀ alias,
    access.aliasVariable x = .ok (some alias) → DemandAliasProtected owner alias
  retained : ∀ alias, alias ∈ point.retained → DemandAliasProtected owner alias

structure DeclarativePlanDemand (m : Module) (owner : Nat)
    (plan : Array DemandPoint) : Prop where
  access : ∃ access, demandAccess? m owner = some access ∧
    ∀ expected, DemandExpectedAt m owner expected →
      (expected.phase = .mutation →
        (expected.node.isDirectShrink = true ∨
          ∃ context args, expected.node.callInfo? = some (context, args)) →
        ∀ shrinkOwner, shrinkOwner ∈ expected.shrinkOwners →
          DeclarativeFrameDemand access expected.toPoint shrinkOwner) ∧
      (∀ request, request ∈ expected.wholeChecks →
        DemandRootSetsSeparate request.forbidden.roots request.checkedRoots)

def DeclarativeDemand (m : Module) : Prop :=
  ∃ plans, PlansWellFormed m plans ∧
    ∀ owner plan, plans[owner]? = some plan → DeclarativePlanDemand m owner plan

private theorem rootSeparate_of_noOverlap {owner alias : RootRef}
    (apart : rootsMayOverlap owner alias = false) : DemandRootSeparate owner alias := by
  cases owner <;> cases alias <;> simp [rootsMayOverlap] at apart
  · exact .locals apart
  · exact .localGlobal
  · exact .localParam
  · exact .globalLocal
  · exact .globals apart
  · exact .paramLocal

private theorem rootSetsSeparate_of_disjoint {owners aliases : List RootRef}
    (apart : DemandRootsDisjoint owners aliases) : DemandRootSetsSeparate owners aliases :=
  fun owner ho alias ha => rootSeparate_of_noOverlap (apart owner ho alias ha)

private theorem invalidatingOwner_bool {owner : DemandOwner}
    (invalidates : DemandInvalidatingOwner owner.ty) : owner.invalidates = true := by
  cases ht : owner.ty with
  | none => simp [DemandOwner.invalidates, ht]
  | some ty =>
    cases ty <;> simp_all [DemandInvalidatingOwner, DemandOwner.invalidates]

private theorem interior_bool {ty : Ty} (interior : DemandInterior ty) :
    ty.interiorTarget?.isSome = true := by
  cases ty <;> simp_all [DemandInterior, Ty.interiorTarget?]

private theorem aliasProtected_of_noConflict {owner : DemandOwner} {alias : RetainedAlias}
    (apart : owner.conflicts alias = false) : DemandAliasProtected owner alias := by
  intro invalidates interior
  have ho := invalidatingOwner_bool invalidates
  have ha := interior_bool interior
  have disjoint : DemandRootsDisjoint owner.roots alias.roots := by
    simpa [DemandOwner.conflicts, DemandOwner.compatible, ho, ha,
      DemandRootsDisjoint] using apart
  exact rootSetsSeparate_of_disjoint disjoint

private theorem frameDemand_of_safe {access : AccessEnv} {point expected : DemandPoint}
    {owner : DemandOwner} (safe : DemandPointShrinkSafe access point owner)
    (same : DemandPoint.sameFrameMembership point expected) :
    DeclarativeFrameDemand access expected owner := by
  constructor
  · intro x hf ha
    exact safe.2 x ((same.2.1 x).mpr hf) ((same.1 x).mpr ha)
  · intro x hf ha alias halias
    exact aliasProtected_of_noConflict
      (safe.1.1 x ((same.2.1 x).mpr hf) ((same.1 x).mpr ha) alias halias)
  · intro alias halias
    exact aliasProtected_of_noConflict (safe.1.2 alias ((same.2.2 alias).mpr halias))

private theorem planDemand_of_approvals {m : Module} {owner : Nat}
    {plan : Array DemandPoint} {expected : List DemandExpectedPoint}
    (walk : DemandNode.expectedPoints m owner = .ok expected)
    (approvals : DemandPlanApprovals m owner plan expected) :
    DeclarativePlanDemand m owner plan := by
  refine ⟨approvals.access, approvals.accessMatches, ?_⟩
  intro occurrence source
  obtain ⟨points, hwalk, member⟩ := source
  rw [walk] at hwalk
  cases hwalk
  constructor
  · intro mutation kind shrinkOwner shrinkMember
    rcases kind with direct | ⟨context, args, call⟩
    · obtain ⟨approval, ha, _, ho, _, same⟩ :=
        approvals.directShrinkAt occurrence member mutation direct shrinkOwner shrinkMember
      have safe := approval.safe
      rw [ha, ho] at safe
      exact frameDemand_of_safe safe same
    · obtain ⟨approval, ha, _, ho, _, same⟩ :=
        approvals.callShrinkAt occurrence member context args call mutation shrinkOwner shrinkMember
      have safe := approval.safe
      rw [ha, ho] at safe
      exact frameDemand_of_safe safe same
  · intro request requestMember
    obtain ⟨approval, _, _, ho, hr, _⟩ :=
      approvals.wholeRootsAt occurrence member request requestMember
    have apart := rootSetsSeparate_of_disjoint approval.disjoint
    simpa [ho, hr] using apart

theorem validate_declarativeDemand (m : Module) (accepted : validate m = .ok ()) :
    DeclarativeDemand m := by
  have checked := (Sound.validate_modOk m accepted).demand
  obtain ⟨plans, derived, wellFormed⟩ := deriveModuleDemand_ok_wellFormed m checked
  obtain ⟨approvals, _⟩ := deriveModuleDemand_ok_approvals m plans derived
  refine ⟨plans, wellFormed, ?_⟩
  intro owner plan selected
  obtain ⟨⟨expected, walk, approved⟩⟩ := approvals owner plan selected
  exact planDemand_of_approvals walk.down approved

theorem DeclarativePlanDemand.directShrink {m : Module} {owner : Nat}
    {plan : Array DemandPoint} (demand : DeclarativePlanDemand m owner plan)
    {expected : DemandExpectedPoint} (source : DemandExpectedAt m owner expected)
    (mutation : expected.phase = .mutation) {place : Place}
    (direct : expected.node.directShrinkPlace? = some place) :
    ∃ access shrinkOwner, demandAccess? m owner = some access ∧
      access.owner place = .ok shrinkOwner ∧
      DeclarativeFrameDemand access expected.toPoint shrinkOwner := by
  obtain ⟨access, accessMatches, safety⟩ := demand.access
  have sourceAt : DemandExpectedSourceAt m owner expected.path expected.node
      expected.phase expected := by
    obtain ⟨points, walk, member⟩ := source
    exact ⟨points, walk, member, rfl, rfl, rfl⟩
  obtain ⟨shrinkOwner, ownerResult, owners⟩ :=
    sourceAt.directShrinkOwner_result mutation direct accessMatches
  refine ⟨access, shrinkOwner, accessMatches, ownerResult, ?_⟩
  exact (safety expected source).1 mutation
    (Or.inl (by simp [DemandNode.isDirectShrink, direct])) shrinkOwner (by simp [owners])

theorem DeclarativePlanDemand.unknownCall {m : Module} {owner : Nat}
    {plan : Array DemandPoint} (demand : DeclarativePlanDemand m owner plan)
    {expected : DemandExpectedPoint} (source : DemandExpectedAt m owner expected)
    (mutation : expected.phase = .mutation) {context : ContextId} {args : List Arg}
    {origin : OriginId} (call : expected.node = .expression (.call context args origin)) :
    ∃ access actual, demandAccess? m owner = some access ∧
      access.argsRoots args = .ok actual ∧
      ∀ ctx callee, access.mod.contexts[context]? = some ctx →
        access.mod.impls[ctx.impl]? = some callee → callee.summary = .unknown →
        ∀ shrinkOwner, shrinkOwner ∈ access.unknownOwners actual →
          DeclarativeFrameDemand access expected.toPoint shrinkOwner := by
  obtain ⟨access, accessMatches, safety⟩ := demand.access
  have sourceAt : DemandExpectedSourceAt m owner expected.path expected.node
      expected.phase expected := by
    obtain ⟨points, walk, member⟩ := source
    exact ⟨points, walk, member, rfl, rfl, rfl⟩
  obtain ⟨actual, actualResult, ownersResult⟩ :=
    sourceAt.callShrinkOwners mutation call accessMatches
  refine ⟨access, actual, accessMatches, actualResult, ?_⟩
  intro ctx callee ctxAt calleeAt unknown shrinkOwner shrinkMember
  have owners : access.unknownOwners actual = expected.shrinkOwners := by
    simp only [AccessEnv.callShrinkOwners, ctxAt, calleeAt, actualResult, unknown] at ownersResult
    exact Except.ok.inj ownersResult
  apply (safety expected source).1 mutation
    (Or.inr ⟨context, args, by simp [call, DemandNode.callInfo?]⟩) shrinkOwner
  simpa [← owners] using shrinkMember

theorem DeclarativeFrameDemand.retainedResizable {access : AccessEnv} {point : DemandPoint}
    {element : Ty} {roots : List RootRef}
    (demand : DeclarativeFrameDemand access point ⟨some (.growshrink element), roots⟩)
    {alias : RetainedAlias} (held : alias ∈ point.retained) (interior : DemandInterior alias.ty) :
    DemandRootSetsSeparate roots alias.roots :=
  demand.retained alias held (by trivial) interior

theorem limitedOwner_doesNotInvalidate (element : Ty) (capacity : Nat) :
    ¬ DemandInvalidatingOwner (some (.limited element capacity)) := by
  simp [DemandInvalidatingOwner]

theorem limitedShrink_keepsWrittenSlots (element : Ty) (capacity : Nat)
    (slots : Array Val) (visible newVisible : Nat) (shrinks : newVisible ≤ visible) :
    Val.truncate newVisible (.limited element capacity slots visible) =
      some (.limited element capacity slots newVisible) := by
  simp [Val.truncate, shrinks]

theorem ownerReference_doesNotDemandInterior (mu : Mutability) (element : Ty) :
    ¬ DemandInterior (.ref mu (.growshrink element)) := by
  simp [DemandInterior, Ty.ownerElem?]

theorem parameterRoots_notSeparate (x y : Nat) :
    ¬ DemandRootSeparate (.param x) (.param y) := by
  intro h
  cases h

theorem parameterGlobal_notSeparate (x y : Nat) :
    ¬ DemandRootSeparate (.param x) (.global y) := by
  intro h
  cases h

end Goose.Core
