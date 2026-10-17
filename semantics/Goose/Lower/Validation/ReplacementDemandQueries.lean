import Goose.Lower.Validation.ReplacementDemandApart
import Goose.Lower.Validation.ReplacementClosure
import Goose.Lower.Validation.ReplacementIndependence
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

theorem ReplacementDemandContext.descendant_place_query_apart {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module planOwner path place rhs origin)
    {suffix : List Nat} {child : Place}
    (source : DemandNodeAt (.expression rhs) suffix (.place child))
    {target : DemandOwner} {roots : List RootRef}
    (targetAt : context.planContext.approvals.access.owner place = .ok target)
    (rootsAt : context.planContext.approvals.access.placeRoots child = .ok roots)
    {func : Func} {queries : ReplacementQueries} {owner : ValueId} {query : ReplacementRootQuery}
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    (sourceKnown : ReplacementRootsWithin query (roots.flatMap func.expandParameterRoot)) :
    ReplacementApart queries owner query := by
  obtain ⟨actualTarget, actualRoots, actualTargetAt, actualRootsAt, disjoint⟩ :=
    context.descendant_place_disjoint source
  have sameTarget := Except.ok.inj (actualTargetAt.symm.trans targetAt)
  have sameRoots := Except.ok.inj (actualRootsAt.symm.trans rootsAt)
  subst actualTarget
  subst actualRoots
  exact replacementApart_of_expanded_source closed ownerKnown sourceKnown disjoint

theorem ReplacementDemandContext.descendant_call_query_apart {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module planOwner path place rhs origin)
    {suffix : List Nat} {callee : ContextId} {args : List Arg} {callOrigin : OriginId}
    (source : DemandNodeAt (.expression rhs) suffix (.expression (.call callee args callOrigin)))
    {target : DemandOwner} {effects : List DemandOwner}
    (targetAt : context.planContext.approvals.access.owner place = .ok target)
    (effectsAt : context.planContext.approvals.access.callEffectOwners callee args = .ok effects)
    {func : Func} {queries : ReplacementQueries} {owner : ValueId} {query : ReplacementRootQuery}
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    (sourceKnown : ReplacementRootsWithin query
      ((effects.flatMap DemandOwner.roots).flatMap func.expandParameterRoot)) :
    ReplacementApart queries owner query := by
  obtain ⟨actualTarget, actualEffects, actualTargetAt, actualEffectsAt, disjoint⟩ :=
    context.descendant_call_disjoint source
  have sameTarget := Except.ok.inj (actualTargetAt.symm.trans targetAt)
  have sameEffects := Except.ok.inj (actualEffectsAt.symm.trans effectsAt)
  subst actualTarget
  subst actualEffects
  apply replacementApart_of_expanded_source closed ownerKnown sourceKnown
  intro ownerRoot ownerMember effectRoot effectMember
  obtain ⟨effect, effectAt, rootAt⟩ := List.mem_flatMap.mp effectMember
  exact disjoint effect effectAt ownerRoot ownerMember effectRoot rootAt

theorem ReplacementDemandContext.descendant_read_load_apart {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module planOwner path place rhs origin)
    {suffix : List Nat} {child : Place}
    (source : DemandNodeAt (.expression rhs) suffix (.expression (.read child)))
    {target : DemandOwner} {addressRoots readRoots : List RootRef}
    (targetAt : context.planContext.approvals.access.owner place = .ok target)
    (addressAt : context.planContext.approvals.access.placeRoots child = .ok addressRoots)
    (readAt : context.planContext.approvals.access.exprRoots (.read child) = .ok readRoots)
    {girModule : GIR.Module} {func : Func} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner address value : ValueId}
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    (addressKnown : ReplacementRootsWithin (queries.value address)
      (addressRoots.flatMap func.expandParameterRoot))
    (readKnown : ReplacementRootsWithin (queries.value value) (readRoots.flatMap func.expandParameterRoot)) :
    ReplacementInstApart girModule types queries owner (.def value (.load address)) := by
  have childSource : DemandNodeAt (.expression rhs) (suffix ++ [0]) (.place child) :=
    source.snoc 0 (by simp [DemandNode.child?, DemandNode.children])
  have addressApart := context.descendant_place_query_apart childSource targetAt addressAt
    closed ownerKnown addressKnown
  have readApart := context.descendant_read_query_apart source targetAt readAt
    closed ownerKnown readKnown
  constructor
  · intro operand member _
    simp only [emptyFactSourceOperands, ReplacementContentFlow.Model.accessOperands,
      Inst.uses, Op.uses, List.mem_singleton] at member
    subst operand
    exact addressApart
  · intro operand member _
    simp only [ReplacementContentFlow.Model.loadedResults, List.mem_singleton] at member
    subst operand
    exact readApart
  · intro result fn args callOrigin same
    cases same

#print axioms replacementApart_of_expanded_source
#print axioms ReplacementDemandContext.descendant_read_query_apart
#print axioms ReplacementDemandContext.descendant_place_query_apart
#print axioms ReplacementDemandContext.descendant_call_query_apart
#print axioms ReplacementDemandContext.descendant_read_load_apart

end Goose.Lower.Validation
