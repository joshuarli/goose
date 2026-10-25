import Goose.Lower.Validation.ReplacementScopedOrigins
import Goose.Lower.Validation.ReplacementOccurrenceApart
import Goose.Lower.Validation.ReplacementPhysicalApart
import Goose.GIR.ReplacementContentFlowProofsSlotAddressQueries

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

theorem ReplacementContentFlowSource.ConsumedReferenceOccurrence.unbacked_apart
    {module : Core.Module} {planOwner : Nat} {path : List Nat}
    {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module planOwner path place rhs origin)
    {env : PEnv} {func : Func} {types : Array (Option VTy)} {upper : Prov} {value : ValueId}
    (occurrence : ConsumedReferenceOccurrence env (.expression rhs) func types upper value)
    (unbacked : ¬ ScopedTypedBacking func types value)
    (access : env.access = context.planContext.approvals.access)
    {target : DemandOwner}
    (targetAt : context.planContext.approvals.access.owner place = .ok target)
    (closed : ParameterRootsClosed func)
    {owner : ValueId} {ownerRoots : List RootRef} {ownerType : Ty}
    (ownerAt : (replacementQueries (lower module) func types).value owner = some ownerRoots)
    (owning : ownerType.ownerElem?.isSome = true)
    (ownerLocalTypes : ∀ slot, RootRef.local slot ∈ ownerRoots →
      ∃ storage, func.slots[slot]? = some storage ∧ storage.ty = ownerType)
    (ownerKnown : ReplacementRootsWithin ((replacementQueries (lower module) func types).value owner)
      (target.roots.flatMap func.expandParameterRoot))
    (valueKnown : ReplacementRootsWithin ((replacementQueries (lower module) func types).ownerDependencies value)
      ((rootsAt upper.vals value).flatMap func.expandParameterRoot))
    {returned : List RootRef}
    (rawKnown : ((replacementContentFlow (lower module)).forFunction func types).value value = some returned)
    (bounded : value < func.numValues)
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup) :
    ReplacementApart (replacementQueries (lower module) func types) owner
      ((replacementQueries (lower module) func types).ownerDependencies value) := by
  cases occurrence with
  | place localEnv suffix child before roots after localAccess source replay _ refined =>
    obtain ⟨_, actualRoots, _, rootsAt, _⟩ := context.descendant_place_disjoint source
    apply context.descendant_place_query_apart source targetAt rootsAt closed ownerKnown
    exact (valueKnown.refined_expanded closed refined).access_place replay
      ((localAccess.trans access) ▸ rootsAt)
  | read localEnv suffix child before roots after localAccess source replay _ refined =>
    obtain ⟨_, actualRoots, _, rootsAt, _⟩ := context.descendant_read_disjoint source
    apply context.descendant_read_query_apart source targetAt rootsAt closed ownerKnown
    exact (valueKnown.refined_expanded closed refined).access_expr replay
      ((localAccess.trans access) ▸ rootsAt)
  | administrative slot storage mutability block member defined storageAt typeAt nonowner =>
    obtain ⟨dependencies, dependencyAt, included⟩ :=
      ReplacementContentFlow.forFunction_slotAddr_dependencies unique member defined rawKnown
    apply replacementApart_of_nonowner_slot ownerAt owning ownerLocalTypes storageAt nonowner
    refine ⟨dependencies, ?_, included⟩
    rw [replacementQueries_ownerDependencies _ _ _ _ bounded]
    exact dependencyAt
  | backing source op block member defined forward sourceType sourceAt carrier =>
    exact False.elim (unbacked ⟨source, op, block, member, defined, forward,
      sourceType, sourceAt, carrier⟩)

#print axioms ReplacementContentFlowSource.ConsumedReferenceOccurrence.unbacked_apart

end Goose.Lower.Validation
