import Goose.Lower.Validation.SourceReplacementCallContentsApart
import Goose.GIR.ReplacementContentFlowProofsObservation

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem normalized_atoms_apart {module : GIR.Module} {func : Func}
    {queries : ReplacementQueries} {owner : ValueId} {raw : Roots} {actual : List RootRef}
    (known : normalize func raw = some actual)
    (apart : ReplacementApart queries owner (some actual)) :
    raw.AtomsWithin (OwnerDependencyApart module func queries owner) := by
  obtain ⟨dependencies, dependencyAt, included⟩ := ownerDependencies_known (module := module) known
  exact ownerDependencies_atoms_apart dependencyAt (apart.of_subset rfl included)

theorem ReplacementDemandContext.rhs_alias_content_atoms_apart {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module planOwner path place rhs origin)
    {variableId : VarId} (used : variableId ∈ rhs.variables)
    (active : variableId ∈ context.statement.expected.frame.active)
    {target : DemandOwner}
    (targetAt : context.planContext.approvals.access.owner place = .ok target)
    (invalidates : target.invalidates = true) {alias : RetainedAlias}
    (aliasAt : context.planContext.approvals.access.aliasVariable variableId = .ok (some alias))
    (interior : alias.ty.interiorTarget?.isSome = true)
    {func : Func} {queries : ReplacementQueries} {owner : ValueId}
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner)
      (target.roots.flatMap func.expandParameterRoot))
    {state : State} {address : Roots} {actual : List RootRef}
    (known : normalize func (content func state address) = some actual)
    (within : actual ⊆ alias.roots.flatMap func.expandParameterRoot) :
    (content func state address).AtomsWithin (OwnerDependencyApart (lower module) func queries owner) := by
  exact normalized_atoms_apart known
    (context.rhs_alias_query_apart used active targetAt invalidates aliasAt interior closed ownerKnown
      ⟨actual, rfl, within⟩)

#print axioms normalized_atoms_apart
#print axioms ReplacementDemandContext.rhs_alias_content_atoms_apart

end Goose.Lower.Validation
