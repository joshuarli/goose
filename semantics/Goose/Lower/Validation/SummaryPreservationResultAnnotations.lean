import Goose.Lower.Validation.SummaryPreservationParameterCeilings

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerContext_parameter_result_alias {module : Core.Module} {ctx : Context}
    {impl : Impl} {result index : Nat} (resultBound : result < impl.results.size)
    (indexBound : index < impl.params.size)
    (subset : subsetRoots ((lowerContextAt module ctx impl).parameterRoots index)
      (ctx.resultRoots[result]?.getD []) = true) :
    RootRef.param index ∈ ((lowerContextAt module ctx impl).roots.results[result]?).getD [] := by
  change RootRef.param index ∈ ((lowerContextRootInfo ctx impl).results[result]?).getD []
  rw [lowerContextRootInfo_result_eq resultBound]
  exact lowerContextRootCeiling_parameter indexBound subset

theorem allowedRoots_lowerContext_result {module : Core.Module} {ctx : Context}
    {impl : Impl} {result : Nat} (bound : result < impl.results.size) :
    ∀ root ∈ allowedRoots (lowerContextAt module ctx impl) (ctx.resultRoots[result]?.getD []),
      root ∈ ((lowerContextAt module ctx impl).roots.results[result]?).getD [] := by
  intro root member
  rcases List.mem_append.mp member with direct | alias
  · obtain ⟨source, sourceMember, mapped⟩ := List.mem_filterMap.mp direct
    have sourceDeclared : source ∈ ((lowerContextAt module ctx impl).roots.results[result]?).getD [] := by
      change source ∈ ((lowerContextRootInfo ctx impl).results[result]?).getD []
      rw [lowerContextRootInfo_result_eq bound]
      exact unionRoots_left _ _ _ sourceMember
    cases source <;> simp_all
  · obtain ⟨index, indexMember, selected⟩ := List.mem_filterMap.mp alias
    split at selected
    · rename_i subset
      simp only [Option.some.injEq] at selected
      subst root
      apply lowerContext_parameter_result_alias bound _ subset
      have indexBound := List.mem_range.mp indexMember
      simpa [lowerContextAt, lowerImpl, lowerImplFromState] using indexBound
    · simp at selected


theorem candidateResult_annotation_contains {module : Core.Module}
    {candidate : Array (List RootRef)} {index : ContextId} {ctx : Context} {impl : Impl}
    (bounded : RootsBelow candidate (moduleResultUpper module))
    (contextLookup : module.contexts[index]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl) (result : 0 < impl.results.size) :
    ∀ root ∈ rootsAt candidate index,
      root ∈ ((lowerContextAt module ctx impl).roots.results[0]?).getD [] := by
  intro root member
  apply allowedRoots_lowerContext_result result root
  have upper := bounded index root member
  simpa only [rootsAt, moduleResultUpper_at contextLookup implLookup, Option.getD_some] using upper

end Goose.Lower.Validation.SummaryPreservation
