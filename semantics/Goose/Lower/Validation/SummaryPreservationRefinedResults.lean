import Goose.Lower.Validation.SummaryPreservationRootRefinement

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def refinedResultUpper (func : Func) (declared : List RootRef) : List RootRef :=
  unionRoots declared (allowedRoots func declared)

theorem refinedResultUpper_refines (func : Func) (declared : List RootRef) :
    RootsRefine func (refinedResultUpper func declared) declared :=
  (RootsRefine.refl func declared).union
    (RootsRefine.of_represented (allowedRoots_represent func declared))

theorem rootsRefine_context_upper {module : Core.Module} {ctx : Context} {impl : Impl}
    {actual declared : List RootRef}
    (refined : RootsRefine (lowerContextAt module ctx impl) actual declared)
    (declaredBounds : ∀ index, RootRef.param index ∈ declared → index < impl.params.size) :
    ∀ root ∈ actual, root ∈ refinedResultUpper (lowerContextAt module ctx impl) declared := by
  intro root member
  rcases refined root member with literal | expanded
  · exact unionRoots_left _ _ root literal
  · have singleton : RootsRepresent (lowerContextAt module ctx impl) [root] declared := by
      intro item itemMember
      have same : item = root := List.mem_singleton.mp itemMember
      subst item
      exact expanded
    exact unionRoots_right _ _ root
      (rootsRepresent_context_allowed singleton declaredBounds root (by simp))

theorem refinedResultUpper_lowerContext_result {module : Core.Module} {ctx : Context}
    {impl : Impl} {result : Nat} (bound : result < impl.results.size) :
    ∀ root ∈ refinedResultUpper (lowerContextAt module ctx impl)
      (ctx.resultRoots[result]?.getD []),
      root ∈ ((lowerContextAt module ctx impl).roots.results[result]?).getD [] := by
  intro root member
  rcases mem_unionRoots_iff.mp member with literal | alias
  · change root ∈ ((lowerContextRootInfo ctx impl).results[result]?).getD []
    rw [lowerContextRootInfo_result_eq bound]
    exact unionRoots_left _ _ root literal
  · exact allowedRoots_lowerContext_result bound root alias

theorem checkedResult_refinedResultUpper {env : PEnv} {actual source : List RootRef}
    (contextOk : CtxOk env.mod env.impl env.ctx)
    (refined : RootsRefine (lowerContextAt env.mod env.ctx env.impl) actual source)
    (checked : checkResultV env source = .ok ()) :
    ∀ root ∈ actual, root ∈ refinedResultUpper (lowerContextAt env.mod env.ctx env.impl)
      (env.ctx.resultRoots[0]?.getD []) := by
  obtain ⟨_, declared, contextRow, sourceSubset⟩ := checkResultV_ok env source checked
  have refinedDeclared := refined.source_mono sourceSubset
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
  have allowed := rootsRefine_context_upper refinedDeclared declaredBounds
  simpa only [contextRow, List.getElem?_cons_zero, Option.getD_some] using allowed


end Goose.Lower.Validation.SummaryPreservation
