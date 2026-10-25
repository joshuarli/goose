import Goose.Core.Demand
import Goose.Lower.Validation.SummaryPreservationRootRefinement

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem parameter_expansion_preserves_disjoint {func : Func}
    (closed : ParameterRootsClosed func) {left right expandedLeft expandedRight : RootRef}
    (apart : Core.rootsMayOverlap left right = false)
    (leftMember : expandedLeft ∈ func.expandParameterRoot left)
    (rightMember : expandedRight ∈ func.expandParameterRoot right) :
    Core.rootsMayOverlap expandedLeft expandedRight = false := by
  cases left <;> cases right <;>
    simp_all [Core.rootsMayOverlap, Func.expandParameterRoot]
  all_goals first
    | obtain rfl | ⟨_, rfl⟩ := closed _ _ leftMember <;> rfl
    | obtain rfl | ⟨_, rfl⟩ := closed _ _ rightMember <;> rfl

theorem DemandRootsDisjoint.expanded {func : Func} {left right : List RootRef}
    (apart : DemandRootsDisjoint left right) (closed : ParameterRootsClosed func) :
    DemandRootsDisjoint (left.flatMap func.expandParameterRoot)
      (right.flatMap func.expandParameterRoot) := by
  intro expandedLeft leftMember expandedRight rightMember
  obtain ⟨leftRoot, leftMember, expandedLeftMember⟩ := List.mem_flatMap.mp leftMember
  obtain ⟨rightRoot, rightMember, expandedRightMember⟩ := List.mem_flatMap.mp rightMember
  exact parameter_expansion_preserves_disjoint closed
    (apart leftRoot leftMember rightRoot rightMember) expandedLeftMember expandedRightMember

theorem DemandRootsDisjoint.refined_expanded {func : Func}
    {left right actualLeft actualRight : List RootRef}
    (apart : DemandRootsDisjoint left right) (closed : ParameterRootsClosed func)
    (leftRefined : RootsRefine func actualLeft left)
    (rightRefined : RootsRefine func actualRight right) :
    DemandRootsDisjoint (actualLeft.flatMap func.expandParameterRoot)
      (actualRight.flatMap func.expandParameterRoot) := by
  intro expandedLeft leftMember expandedRight rightMember
  obtain ⟨leftRoot, leftMember, expandedLeftMember⟩ := List.mem_flatMap.mp leftMember
  obtain ⟨rightRoot, rightMember, expandedRightMember⟩ := List.mem_flatMap.mp rightMember
  exact DemandRootsDisjoint.expanded apart closed expandedLeft
    (leftRefined.expanded closed leftRoot leftMember expandedLeft expandedLeftMember)
    expandedRight
    (rightRefined.expanded closed rightRoot rightMember expandedRight expandedRightMember)

#print axioms parameter_expansion_preserves_disjoint
#print axioms DemandRootsDisjoint.expanded
#print axioms DemandRootsDisjoint.refined_expanded

end Goose.Lower.Validation.SummaryPreservation
