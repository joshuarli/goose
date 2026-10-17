import Goose.Lower.Validation.SummaryPreservationRefinedResults

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem allowedRoots_lowerContext_ceiling {module : Core.Module} {ctx : Context}
    {impl : Impl} {declared : List RootRef} :
    ∀ root ∈ allowedRoots (lowerContextAt module ctx impl) declared,
      root ∈ lowerContextRootCeiling ctx impl declared := by
  intro root member
  rcases List.mem_append.mp member with direct | alias
  · obtain ⟨source, sourceMember, mapped⟩ := List.mem_filterMap.mp direct
    have present : source ∈ lowerContextRootCeiling ctx impl declared :=
      unionRoots_left _ _ _ sourceMember
    cases source <;> simp_all
  · obtain ⟨index, indexMember, selected⟩ := List.mem_filterMap.mp alias
    split at selected
    · rename_i subset
      simp only [Option.some.injEq] at selected
      subst root
      apply lowerContextRootCeiling_parameter _ subset
      have indexBound := List.mem_range.mp indexMember
      simpa [lowerContextAt, lowerImpl, lowerImplFromState] using indexBound
    · simp at selected

theorem refinedResultUpper_lowerContext_ceiling {module : Core.Module} {ctx : Context}
    {impl : Impl} {declared : List RootRef} :
    ∀ root ∈ refinedResultUpper (lowerContextAt module ctx impl) declared,
      root ∈ lowerContextRootCeiling ctx impl declared := by
  intro root member
  rcases mem_unionRoots_iff.mp member with literal | alias
  · exact unionRoots_left _ _ _ literal
  · exact allowedRoots_lowerContext_ceiling root alias

theorem rootsRefine_lowerContext_ceiling {module : Core.Module} {ctx : Context} {impl : Impl}
    {actual declared : List RootRef}
    (refined : RootsRefine (lowerContextAt module ctx impl) actual declared)
    (declaredBounds : ∀ index, RootRef.param index ∈ declared → index < impl.params.size) :
    actual ⊆ lowerContextRootCeiling ctx impl declared := by
  intro root member
  exact refinedResultUpper_lowerContext_ceiling root
    (rootsRefine_context_upper refined declaredBounds root member)

#print axioms rootsRefine_lowerContext_ceiling

end Goose.Lower.Validation.SummaryPreservation
