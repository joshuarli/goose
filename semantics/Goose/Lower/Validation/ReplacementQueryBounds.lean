import Goose.Lower.Validation.ReplacementIndependence
import Goose.GIR.ReplacementContentFlowProofsObservation

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementRootsWithin.ownerDependencies {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {value : ValueId} {source : List RootRef}
    (bounded : value < func.numValues)
    (known : ReplacementRootsWithin ((replacementQueries module func types).value value) source) :
    ReplacementRootsWithin ((replacementQueries module func types).ownerDependencies value) source := by
  obtain ⟨roots, valueAt, included⟩ := known
  rw [replacementQueries_value module func types value bounded] at valueAt
  obtain ⟨dependencies, dependencyAt, subset⟩ :=
    ReplacementFunctionFlow.ownerDependencies_of_value valueAt
  refine ⟨dependencies, ?_, subset.trans included⟩
  rw [replacementQueries_ownerDependencies module func types value bounded]
  exact dependencyAt

#print axioms ReplacementRootsWithin.ownerDependencies

end Goose.Lower.Validation
