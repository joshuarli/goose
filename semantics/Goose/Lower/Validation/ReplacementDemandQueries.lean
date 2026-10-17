import Goose.Lower.Validation.ReplacementDemandApart
import Goose.Lower.Validation.ReplacementClosure
import Goose.Lower.Validation.SummaryPreservationDisjointExpansion

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation

theorem replacementApart_of_expanded_source {func : Func}
    {queries : ReplacementQueries} {owner : ValueId} {query : ReplacementRootQuery}
    {ownerRoots sourceRoots : List RootRef} (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (ownerRoots.flatMap func.expandParameterRoot))
    (sourceKnown : ReplacementRootsWithin query (sourceRoots.flatMap func.expandParameterRoot))
    (disjoint : DemandRootsDisjoint ownerRoots sourceRoots) : ReplacementApart queries owner query :=
  replacementApart_of_source ownerKnown sourceKnown
    (SummaryPreservation.DemandRootsDisjoint.expanded disjoint closed)

theorem ReplacementDemandContext.descendant_read_query_apart {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module planOwner path place rhs origin)
    {suffix : List Nat} {child : Place}
    (source : DemandNodeAt (.expression rhs) suffix (.expression (.read child)))
    {target : DemandOwner} {roots : List RootRef}
    (targetAt : context.planContext.approvals.access.owner place = .ok target)
    (rootsAt : context.planContext.approvals.access.exprRoots (.read child) = .ok roots)
    {func : Func} {queries : ReplacementQueries} {owner : ValueId} {query : ReplacementRootQuery}
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    (sourceKnown : ReplacementRootsWithin query (roots.flatMap func.expandParameterRoot)) :
    ReplacementApart queries owner query := by
  obtain ⟨actualTarget, actualRoots, actualTargetAt, actualRootsAt, disjoint⟩ :=
    context.descendant_read_disjoint source
  have sameTarget := Except.ok.inj (actualTargetAt.symm.trans targetAt)
  have sameRoots := Except.ok.inj (actualRootsAt.symm.trans rootsAt)
  subst actualTarget
  subst actualRoots
  exact replacementApart_of_expanded_source closed ownerKnown sourceKnown disjoint

#print axioms replacementApart_of_expanded_source
#print axioms ReplacementDemandContext.descendant_read_query_apart

end Goose.Lower.Validation
