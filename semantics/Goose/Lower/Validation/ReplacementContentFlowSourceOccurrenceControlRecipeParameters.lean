import Goose.Lower.Validation.SummaryPreservationDeclaredSeeds
import Goose.Lower.Validation.SummaryPreservationRefinedCeilings

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem contextualRecipeMetadataBounds (module : Core.Module) (context : Context) (impl : Impl)
    (declared metadata : List RootRef)
    (bounded : ∀ index, RootRef.param index ∈ declared → index < impl.params.size)
    (same : metadata = lowerContextRootCeiling context impl declared) :
    metadata ⊆ refinedResultUpper (lowerContextAt module context impl) declared ∧
      ∀ actual, GIR.RootsRefine (lowerContextAt module context impl) actual declared → actual ⊆ metadata := by
  rw [same]
  exact ⟨lowerContextRootCeiling_below_refined module context impl declared,
    fun _ refined => rootsRefine_lowerContext_ceiling refined bounded⟩

theorem genericRecipeMetadataBounds {env : PEnv} {func : Func} (declared metadata : List RootRef)
    (noParameters : env.impl.params = #[])
    (parameterIdentity : ∀ index, func.parameterRoots index = [.param index])
    (same : metadata = lowerContextRootCeiling env.ctx env.impl declared) :
    metadata ⊆ refinedResultUpper func declared ∧
      ∀ actual, GIR.RootsRefine func actual declared → actual ⊆ metadata := by
  have ceiling : lowerContextRootCeiling env.ctx env.impl declared = declared := by
    simp [lowerContextRootCeiling, noParameters, unionRoots]
  rw [ceiling] at same
  rw [same]
  refine ⟨fun root member => unionRoots_left _ _ root member, ?_⟩
  intro actual refined root member
  rcases refined root member with literal | represented
  · exact literal
  · apply represented root
    cases root <;> simp [Func.expandParameterRoot, parameterIdentity]

#print axioms contextualRecipeMetadataBounds
#print axioms genericRecipeMetadataBounds

end Goose.Lower.Validation.ReplacementContentFlowSource
