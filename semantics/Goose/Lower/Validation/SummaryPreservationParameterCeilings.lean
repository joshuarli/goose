import Goose.Lower.Validation.SummaryPreservationResultBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerContextRootCeiling_parameter {module : Core.Module} {ctx : Context}
    {impl : Impl} {declared : List RootRef} {index : Nat}
    (indexBound : index < impl.params.size)
    (subset : subsetRoots ((lowerContextAt module ctx impl).parameterRoots index)
      declared = true) :
    RootRef.param index ∈ lowerContextRootCeiling ctx impl declared := by
  let param := impl.params[index]'indexBound
  have parameter : impl.params[index]? = some param := Array.getElem?_eq_getElem indexBound
  unfold lowerContextRootCeiling
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
    change (if entry.2.all declared.contains then
      some (RootRef.param index) else none) = some (RootRef.param index)
    exact if_pos subset

#print axioms lowerContextRootCeiling_parameter

end Goose.Lower.Validation.SummaryPreservation
