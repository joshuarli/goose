import Goose.Lower.Validation.ReplacementContentFlowSourceShape
import Goose.Lower.Validation.SummaryPreservationRootRefinement

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open SummaryPreservation

theorem lowerContextAt_result_refines_source {module : Core.Module} {ctx : Context} {impl : Impl}
    {result : Nat} (bound : result < impl.results.size) :
    RootsRefine (lowerContextAt module ctx impl)
      (((lowerContextAt module ctx impl).roots.results[result]?).getD [])
      (ctx.resultRoots[result]?.getD []) := by
  intro root member
  change root ∈ ((lowerContextRootInfo ctx impl).results[result]?).getD [] at member
  rw [lowerContextRootInfo_result_eq bound] at member
  simp only [Option.getD_some] at member
  rcases mem_unionRoots_iff.mp member with direct | alias
  · exact Or.inl direct
  · obtain ⟨⟨parameter, index⟩, parameterMember, selected⟩ := List.mem_filterMap.mp alias
    have parameterRow : impl.params[index]? = some parameter := by
      simpa only [Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp parameterMember
    cases annotation : ctx.varRoots.find? (·.1 == parameter.var) with
    | none => simp [annotation] at selected
    | some row =>
      simp only [annotation] at selected
      split at selected
      · rename_i subset
        simp only [Option.some.injEq] at selected
        subst root
        refine Or.inr ?_
        rw [Func.expandParameterRoot, lowerContextAt_parameterRoots_eq (roots := row.2) parameterRow
          (by simp [annotation])]
        intro concrete concreteMember
        exact Core.Sound.subsetRoots_mem subset concrete concreteMember
      · simp at selected

#print axioms lowerContextAt_result_refines_source

end Goose.Lower.Validation.ReplacementContentFlowSource
