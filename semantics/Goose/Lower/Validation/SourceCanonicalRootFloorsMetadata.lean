import Goose.Core.Demand
import Goose.Core.Sound.Frame
import Goose.Lower.Validation.SourceCanonicalRootFloorsRows
import Goose.Lower.Validation.SourceCanonicalRootFloorsRecipes

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR

def sourceNodeRootTable (env : PEnv) (root : DemandNode) : SourceRootTable :=
  match root with
  | .expression expression =>
      (collectSourceExprRoots env expression
        (Array.replicate (scopeParents (exprScopes none expression)).size none)).2
  | .place place =>
      (collectSourcePlaceRoots env place
        (Array.replicate (scopeParents (placeScopes none place)).size none)).2
  | .view view =>
      (collectSourceViewRoots env view
        (Array.replicate (scopeParents (viewScopes none view)).size none)).2
  | .bound bound =>
      (collectSourceBoundRoots env bound
        (Array.replicate (scopeParents (boundScopes none bound)).size none)).2
  | .statement statement =>
      (collectSourceStmtRoots env statement
        (Array.replicate (scopeParents (stmtScopes none statement)).size none)).2
  | .block body =>
      (collectSourceBlockRoots env body
        (Array.replicate (scopeParents (blockScopes none body)).size none)).2

structure RecipeMetadataProjects (env : PEnv) (root : DemandNode) (func : GIR.Func)
    (state : LS) : Prop where
  covered : ∀ recipe ∈ state.valueRootRecipes,
    ∃ roots, (recipe.1, roots) ∈ func.roots.values.getD #[]
  project : ∀ recipe ∈ state.valueRootRecipes,
    ∀ roots, (recipe.1, roots) ∈ func.roots.values.getD #[] →
      roots = lowerValueRootCeiling env (sourceNodeRootTable env root) recipe.2

theorem RecipeMetadataProjects.restrict {env : PEnv} {root : DemandNode}
    {func : GIR.Func} {before after : LS}
    (projects : RecipeMetadataProjects env root func after)
    (retained : ∀ recipe ∈ before.valueRootRecipes, recipe ∈ after.valueRootRecipes) :
    RecipeMetadataProjects env root func before := by
  constructor
  · intro recipe member
    exact projects.covered recipe (retained recipe member)
  · intro recipe member roots row
    exact projects.project recipe (retained recipe member) roots row

theorem RecipeMetadataProjects.refSliceVar_row {env : PEnv} {root : DemandNode}
    {func : GIR.Func} {state : LS} (projects : RecipeMetadataProjects env root func state)
    {value : ValueId} {varId : VarId}
    (recorded : (value, .refSliceVar varId) ∈ state.valueRootRecipes)
    {rowRoots : List RootRef} (row : (value, rowRoots) ∈ func.roots.values.getD #[]) :
    rowRoots = lowerValueRootCeiling env #[] (.refSliceVar varId) :=
  projects.project (value, .refSliceVar varId) recorded rowRoots row

theorem RecipeMetadataProjects.refSliceVar_annotation_subset {env : PEnv} {root : DemandNode}
    {func : GIR.Func} {state : LS} (projects : RecipeMetadataProjects env root func state)
    {value : ValueId} {varId : VarId}
    (recorded : (value, .refSliceVar varId) ∈ state.valueRootRecipes)
    {rowRoots : List RootRef} (row : (value, rowRoots) ∈ func.roots.values.getD #[]) :
    ((env.ann varId).getD []) ⊆ rowRoots := by
  rw [projects.refSliceVar_row recorded row]
  exact Goose.Core.Sound.unionRoots_left _ _

theorem lowerContextAt_recipeMetadataProjects (module : Core.Module) (ctx : Context) (impl : Impl) :
    RecipeMetadataProjects ⟨module, impl, ctx, []⟩ (.block impl.body)
      (lowerContextAt module ctx impl) (lowerImplState module impl) := by
  constructor
  · intro recipe member
    exact ⟨_, lowerValueRootRows_contains ⟨module, impl, ctx, []⟩ _ _ member⟩
  · intro recipe member roots row
    exact lowerValueRootRows_exact ⟨module, impl, ctx, []⟩ _ _
      (lowerImplState_recipes module impl).1 member row

theorem lowerGlobal_recipeMetadataProjects (module : Core.Module) (global : Core.Global) :
    RecipeMetadataProjects ⟨module, initImpl, initContext, []⟩ (.expression global.init)
      (lowerGlobal module global).init (globalRecipeState module global) := by
  constructor
  · intro recipe member
    exact ⟨_, lowerValueRootRows_contains ⟨module, initImpl, initContext, []⟩ _ _ member⟩
  · intro recipe member roots row
    exact lowerValueRootRows_exact ⟨module, initImpl, initContext, []⟩ _ _
      (globalRecipeState_recipes module global).1 member row

end Goose.Lower.Validation.SourceCanonicalRootFloors
