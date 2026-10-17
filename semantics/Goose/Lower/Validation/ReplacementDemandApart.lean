import Goose.Lower.Validation.ReplacementDemandSitesOwners
import Goose.Core.Sound.ShrinkBridge

namespace Goose.Core.Sound

theorem NodeContext.readWholeRootsChecked
    {module : Core.Module} {plans : Array (Array DemandPoint)}
    {planContext : PlanContext module plans} {path : List Nat} {place : Place}
    (context : NodeContext planContext path (.expression (.read place)) .expression)
    (forbiddenOwner : DemandOwner) (forbidden : forbiddenOwner ∈ context.expected.forbidden) :
    ∃ roots, planContext.approvals.access.exprRoots (.read place) = .ok roots ∧
      DemandRootsDisjoint forbiddenOwner.roots roots := by
  obtain ⟨roots, rootsAt, request, requestAt, requestOwner, requestRoots⟩ :=
    context.sourceAt.readWholeRootsRequest planContext.approvals.accessMatches forbidden
  obtain ⟨approval, _, _, ownerEq, rootsEq, _⟩ := context.wholeRootsApproval requestAt
  refine ⟨roots, rootsAt, ?_⟩
  simpa [ownerEq, requestOwner, rootsEq, requestRoots] using approval.disjoint

end Goose.Core.Sound

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

private theorem demand_primary_phase (node : DemandNode) : DemandNodeHasPhase node node.primaryPhase := by
  cases node <;> simp [DemandNodeHasPhase, DemandNode.primaryPhase, DemandNode.phaseMatches]

theorem demand_descendant_forbidden {module : Core.Module} {plans : Array (Array DemandPoint)}
    {pc : PlanContext module plans} {parent node : DemandNode} {suffix : List Nat}
    (source : DemandNodeAt parent suffix node) :
    ∀ {front} (context : NodeContext pc front parent parent.primaryPhase) {owner},
      owner ∈ context.expected.forbidden →
      ∃ descendant : NodeContext pc (front ++ suffix) node node.primaryPhase,
        owner ∈ descendant.expected.forbidden := by
  induction source with
  | here parent =>
    intro front context owner forbidden
    rw [List.append_nil]
    exact ⟨context, forbidden⟩
  | @child parent middle node index suffix row source ih =>
    intro front context owner forbidden
    let transition := context.child rfl index middle middle.primaryPhase row (demand_primary_phase middle)
    have inherited := transition.forbiddenSubset owner forbidden
    have selected := ih transition.context inherited
    have pathEq : front ++ index :: suffix = (front ++ [index]) ++ suffix := by
      simp [List.append_assoc]
    rw [pathEq]
    exact selected

theorem ReplacementDemandContext.descendant_place_disjoint {module : Core.Module}
    {owner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module owner path place rhs origin)
    {suffix : List Nat} {child : Place}
    (source : DemandNodeAt (.expression rhs) suffix (.place child)) :
    ∃ target roots,
      context.planContext.approvals.access.owner place = .ok target ∧
      context.planContext.approvals.access.placeRoots child = .ok roots ∧
      DemandRootsDisjoint target.roots roots := by
  obtain ⟨target, ownerAt, forbidden⟩ := context.owner_forbidden
  have inherited : target ∈ context.rhsTransition.context.expected.forbidden := forbidden
  obtain ⟨descendant, selected⟩ := demand_descendant_forbidden source context.rhsTransition.context inherited
  obtain ⟨roots, rootsAt, disjoint⟩ := descendant.placeWholeRootsChecked target selected
  exact ⟨target, roots, ownerAt, rootsAt, disjoint⟩

theorem ReplacementDemandContext.descendant_read_disjoint {module : Core.Module}
    {owner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module owner path place rhs origin)
    {suffix : List Nat} {child : Place}
    (source : DemandNodeAt (.expression rhs) suffix (.expression (.read child))) :
    ∃ target roots,
      context.planContext.approvals.access.owner place = .ok target ∧
      context.planContext.approvals.access.exprRoots (.read child) = .ok roots ∧
      DemandRootsDisjoint target.roots roots := by
  obtain ⟨target, ownerAt, forbidden⟩ := context.owner_forbidden
  obtain ⟨descendant, selected⟩ := demand_descendant_forbidden source context.rhsTransition.context forbidden
  obtain ⟨roots, rootsAt, disjoint⟩ := descendant.readWholeRootsChecked target selected
  exact ⟨target, roots, ownerAt, rootsAt, disjoint⟩

theorem ReplacementDemandContext.descendant_call_disjoint {module : Core.Module}
    {owner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module owner path place rhs origin)
    {suffix : List Nat} {callee : ContextId} {args : List Arg} {callOrigin : OriginId}
    (source : DemandNodeAt (.expression rhs) suffix (.expression (.call callee args callOrigin))) :
    ∃ target effects,
      context.planContext.approvals.access.owner place = .ok target ∧
      context.planContext.approvals.access.callEffectOwners callee args = .ok effects ∧
      ∀ effect ∈ effects, DemandRootsDisjoint target.roots effect.roots := by
  obtain ⟨target, ownerAt, forbidden⟩ := context.owner_forbidden
  have inherited : target ∈ context.rhsTransition.context.expected.forbidden := forbidden
  obtain ⟨descendant, selected⟩ := demand_descendant_forbidden source context.rhsTransition.context inherited
  let mutation := descendant.phase rfl .mutation
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have mutationForbidden : target ∈ mutation.context.expected.forbidden := by
    rw [mutation.forbiddenEq]
    exact selected
  obtain ⟨effects, effectsAt, requests⟩ := mutation.context.sourceAt.callWholeRootsRequests
    context.planContext.approvals.accessMatches mutationForbidden
  refine ⟨target, effects, ownerAt, effectsAt, ?_⟩
  intro effect member
  obtain ⟨approval, _, _, ownerEq, rootsEq, _⟩ := mutation.context.wholeRootsApproval (requests effect member)
  simpa only [ownerEq, rootsEq] using approval.disjoint

#print axioms DemandExpectedSourceAt.readWholeRootsRequest
#print axioms NodeContext.readWholeRootsChecked
#print axioms ReplacementDemandContext.descendant_read_disjoint
#print axioms demand_descendant_forbidden
#print axioms ReplacementDemandContext.descendant_place_disjoint
#print axioms ReplacementDemandContext.descendant_call_disjoint

end Goose.Lower.Validation
