import Goose.Lower.Validation.SummaryPreservationResultAnnotations

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerContextRootInfo_parameter_row_bound {ctx : Context} {impl : Impl}
    {row : Nat × List RootRef} (member : row ∈ (lowerContextRootInfo ctx impl).params.toList) :
    row.1 < impl.params.size := by
  change row ∈ impl.params.toList.zipIdx.filterMap (fun (param, index) =>
    (ctx.varRoots.find? (·.1 == param.var)).map fun (_, roots) => (index, roots)) at member
  obtain ⟨⟨param, index⟩, parameterMember, selected⟩ := List.mem_filterMap.mp member
  have lookup := List.mk_mem_zipIdx_iff_getElem?.mp parameterMember
  cases annotation : ctx.varRoots.find? (·.1 == param.var) with
  | none => simp [annotation] at selected
  | some entry =>
    simp only [annotation, Option.map_some, Option.some.injEq] at selected
    cases selected
    simpa using (List.getElem?_eq_some_iff.mp lookup).1

theorem lowerContext_parameterRoots_outside {module : Core.Module} {ctx : Context}
    {impl : Impl} {index : Nat} (outside : impl.params.size ≤ index) :
    (lowerContextAt module ctx impl).parameterRoots index = [.param index] := by
  have absent : (lowerContextRootInfo ctx impl).params.find? (·.1 == index) = none := by
    rw [← Array.find?_toList]
    apply List.find?_eq_none.mpr
    intro row member key
    have bound := lowerContextRootInfo_parameter_row_bound member
    have same : row.1 = index := eq_of_beq key
    rw [same] at bound
    omega
  change (match (lowerContextRootInfo ctx impl).params.find? (·.1 == index) with
    | some (_, roots) => roots
    | none => [.param index]) = [.param index]
  rw [absent]

theorem rootsRepresent_context_parameter_bounds {module : Core.Module} {ctx : Context}
    {impl : Impl} {actual declared : List RootRef}
    (represented : RootsRepresent (lowerContextAt module ctx impl) actual declared)
    (declaredBounds : ∀ index, RootRef.param index ∈ declared → index < impl.params.size) :
    ∀ index, RootRef.param index ∈ actual → index < impl.params.size := by
  intro index member
  by_cases bound : index < impl.params.size
  · exact bound
  apply False.elim
  have outside := bound
  have generic := lowerContext_parameterRoots_outside (module := module) (ctx := ctx) (impl := impl)
    (Nat.le_of_not_gt outside)
  have concrete : RootRef.param index ∈ (lowerContextAt module ctx impl).expandParameterRoot (.param index) := by
    change RootRef.param index ∈ (lowerContextAt module ctx impl).parameterRoots index
    rw [generic]
    simp
  exact outside (declaredBounds index (represented (.param index) member (.param index) concrete))

theorem rootsRepresent_context_allowed {module : Core.Module} {ctx : Context} {impl : Impl}
    {actual declared : List RootRef}
    (represented : RootsRepresent (lowerContextAt module ctx impl) actual declared)
    (declaredBounds : ∀ index, RootRef.param index ∈ declared → index < impl.params.size) :
    ∀ root ∈ actual, root ∈ allowedRoots (lowerContextAt module ctx impl) declared := by
  apply allowedRoots_complete represented
  intro index member
  have bound := rootsRepresent_context_parameter_bounds represented declaredBounds index member
  simpa [lowerContextAt, lowerImpl, lowerImplFromState] using bound


theorem checkedResult_allowedRoots {env : PEnv} {actual source : List RootRef}
    (contextOk : CtxOk env.mod env.impl env.ctx)
    (represented : RootsRepresent (lowerContextAt env.mod env.ctx env.impl) actual source)
    (checked : checkResultV env source = .ok ()) :
    ∀ root ∈ actual, root ∈ allowedRoots (lowerContextAt env.mod env.ctx env.impl)
      (env.ctx.resultRoots[0]?.getD []) := by
  obtain ⟨_, declared, contextRow, sourceSubset⟩ := checkResultV_ok env source checked
  have representedDeclared := rootsRepresent_mono represented sourceSubset
  have count := contextOk.resultLen
  rw [contextRow] at count
  have resultBound : 0 < env.impl.results.size := by
    simp only [List.length_singleton] at count
    omega
  let ty := env.impl.results[0]'resultBound
  have resultRow : env.impl.results.toList[0]? = some ty := by
    rw [Array.getElem?_toList]
    exact Array.getElem?_eq_getElem resultBound
  have rowMember : (ty, declared) ∈ env.impl.results.toList.zip env.ctx.resultRoots :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨resultRow, by simp [contextRow]⟩)
  have declaredShape := (Core.Declarative.declaredResults_sound env.mod env.impl env.ctx
    contextOk.resultShape).2 ty declared rowMember
  have declaredBounds : ∀ index, RootRef.param index ∈ declared → index < env.impl.params.size := by
    intro index member
    exact (declaredShape.2 (.param index) member).1
  have allowed := rootsRepresent_context_allowed representedDeclared declaredBounds
  simpa only [contextRow, List.getElem?_cons_zero, Option.getD_some] using allowed

end Goose.Lower.Validation.SummaryPreservation
