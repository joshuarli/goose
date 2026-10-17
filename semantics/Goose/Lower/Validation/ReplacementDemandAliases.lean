import Goose.Lower.Validation.ReplacementDemandApart

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

theorem ReplacementDemandContext.rhs_variable_aliases {module : Core.Module}
    {owner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module owner path place rhs origin)
    {variableId : VarId} (used : variableId ∈ rhs.variables)
    (active : variableId ∈ context.statement.expected.frame.active) :
    ∃ target aliases,
      context.planContext.approvals.access.owner place = .ok target ∧
      context.planContext.approvals.access.aliasVariable variableId = .ok aliases ∧
      ∀ alias, aliases = some alias → target.conflicts alias = false := by
  obtain ⟨target, ownerAt, _⟩ := context.owner_forbidden
  let mutation := context.statement.phase rfl .mutation
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have phaseFrame := mutation.phaseFrameEq
  simp only [DemandNode.phaseFrame, DemandNode.phaseFuture, BEq.rfl, ↓reduceIte, pure, Except.pure] at phaseFrame
  have frameEq : mutation.context.expected.frame =
      { context.statement.expected.frame with future := rhs.variables ++ context.statement.expected.frame.future } :=
    mutation.expectedFrameEq.trans (Except.ok.inj phaseFrame).symm
  obtain ⟨approval, _, ownerEq, _, sameFrame⟩ := mutation.context.directShrinkApproval
    (by simp [DemandNode.directShrinkPlace?]) ownerAt
  have accessEq : approval.access = context.planContext.approvals.access :=
    Option.some.inj (approval.accessMatches.symm.trans context.planContext.approvals.accessMatches)
  have future : variableId ∈ approval.point.future := (sameFrame.2.1 variableId).mpr (by
    change variableId ∈ mutation.context.expected.frame.future
    rw [frameEq]
    exact List.mem_append_left _ used)
  have live : variableId ∈ approval.point.active := (sameFrame.1 variableId).mpr (by
    change variableId ∈ mutation.context.expected.frame.active
    simpa only [frameEq] using active)
  obtain ⟨aliases, aliasAt⟩ := approval.safe.aliasVariable_succeeds future live
  refine ⟨target, aliases, ownerAt, ?_, ?_⟩
  · simpa only [accessEq] using aliasAt
  · intro alias sameAlias
    have noConflict := approval.safe.1.1 variableId future live alias (aliasAt.trans (congrArg Except.ok sameAlias))
    simpa only [ownerEq] using noConflict

theorem ReplacementDemandContext.rhs_alias_disjoint {module : Core.Module}
    {owner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module owner path place rhs origin)
    {variableId : VarId} (used : variableId ∈ rhs.variables)
    (active : variableId ∈ context.statement.expected.frame.active)
    {target : DemandOwner} (ownerAt : context.planContext.approvals.access.owner place = .ok target)
    (invalidates : target.invalidates = true) {alias : RetainedAlias}
    (aliasAt : context.planContext.approvals.access.aliasVariable variableId = .ok (some alias))
    (interior : alias.ty.interiorTarget?.isSome = true) : DemandRootsDisjoint target.roots alias.roots := by
  obtain ⟨actual, aliases, actualAt, found, compatible⟩ := context.rhs_variable_aliases used active
  have ownerEq : actual = target := Except.ok.inj (actualAt.symm.trans ownerAt)
  have aliasEq : aliases = some alias := Except.ok.inj (found.symm.trans aliasAt)
  exact DemandOwner.conflicts_false_disjoint invalidates interior (by
    simpa only [ownerEq] using compatible alias aliasEq)

#print axioms ReplacementDemandContext.rhs_variable_aliases
#print axioms ReplacementDemandContext.rhs_alias_disjoint

end Goose.Lower.Validation
