import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.SummaryPreservationReplayBuilder
import Goose.Lower.Validation.SummaryPreservationRefinedResults

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem ReplayBuilder.recordSourceValueRecipe {module : GIR.Module} {results : Array (List RootRef)}
    {types : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {state : LS} {upper : Prov}
    (ready : ReplayBuilder module results types func target le scopeCount slots state upper)
    (value : ValueId) (scope : ScopeId) (sourceRoots : List RootRef) (type : VTy)
    (ceiling : type.refLike = true → state.cur.isSome = true → refinedResultUpper func sourceRoots ⊆ rootsAt upper.vals value)
    (typed : state.cur.isSome = true → ∀ actual, state.vals[value]? = some (some actual) → actual.refLike = true → type.refLike = true)
    (refined : state.cur.isSome = true → RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (metadata : (Goose.Lower.recordValueRootRecipe value scope le state).2.valueRootRecipes =
        state.valueRootRecipes.push (value, .conditionalScope scope) →
      ∀ row ∈ func.roots.values.getD #[], row.1 = value → row.2 ⊆ refinedResultUpper func sourceRoots ∧
        ∀ actual, RootsRefine func actual sourceRoots → actual ⊆ row.2) :
    ReplayBuilder module results types func target le scopeCount slots
      (Goose.Lower.recordValueRootRecipe value scope le state).2 upper := by
  apply ready.recordValueRootRecipeWhen value scope
  intro event row member same
  obtain ⟨live, actual, actualRow, reference⟩ := recordValueRootRecipe_recorded_reference event
  obtain ⟨metadataBound, refinementBound⟩ := metadata event row member same
  exact ⟨fun _ member => ceiling (typed live actual actualRow reference) live (metadataBound member),
    refinementBound _ (refined live)⟩

#print axioms ReplayBuilder.recordSourceValueRecipe

end Goose.Lower.Validation.SummaryPreservation
