import Goose.Lower.Validation.SummaryPreservationResultBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerContext_parameter_result_alias {module : Core.Module} {ctx : Context}
    {impl : Impl} {result index : Nat} (resultBound : result < impl.results.size)
    (indexBound : index < impl.params.size)
    (subset : subsetRoots ((lowerContextAt module ctx impl).parameterRoots index)
      (ctx.resultRoots[result]?.getD []) = true) :
    RootRef.param index ∈ ((lowerContextAt module ctx impl).roots.results[result]?).getD [] := by
  let param := impl.params[index]'indexBound
  have parameter : impl.params[index]? = some param := Array.getElem?_eq_getElem indexBound
  change RootRef.param index ∈ ((lowerContextRootInfo ctx impl).results[result]?).getD []
  rw [lowerContextRootInfo_result_eq resultBound]
  simp only [Option.getD_some]
  cases annotation : ctx.varRoots.find? (·.1 == param.var) with
  | none =>
    have row := lowerContextRootInfo_parameter_lookup (ctx := ctx) parameter
    rw [annotation] at row
    have generic : (lowerContextAt module ctx impl).parameterRoots index = [.param index] := by
      change (match (lowerContextRootInfo ctx impl).params.find? (·.1 == index) with
        | some (_, roots) => roots
        | none => [.param index]) = _
      rw [row]
      rfl
    rw [generic] at subset
    exact unionRoots_left _ _ _ (subsetRoots_mem subset _ (by simp))
  | some entry =>
    have expansion := lowerContextAt_parameterRoots_eq (module := module) (ctx := ctx) parameter
      (roots := entry.2) (by simp [annotation])
    rw [expansion] at subset
    apply unionRoots_right
    apply List.mem_filterMap.mpr
    refine ⟨(param, index), List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using parameter), ?_⟩
    simp only [annotation]
    change (if entry.2.all (ctx.resultRoots[result]?.getD []).contains then
      some (RootRef.param index) else none) = some (RootRef.param index)
    exact if_pos subset

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
      simpa [lowerContextAt, lowerImpl] using indexBound
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
