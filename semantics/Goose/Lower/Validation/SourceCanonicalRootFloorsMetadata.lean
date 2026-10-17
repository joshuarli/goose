import Goose.Core.Demand
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

def RecipeMetadataProjects (env : PEnv) (root : DemandNode) (func : GIR.Func)
    (state : LS) : Prop :=
  ∀ recipe ∈ state.valueRootRecipes,
    ∀ roots, (recipe.1, roots) ∈ func.roots.values.getD #[] →
      roots = lowerContextRootCeiling env.ctx env.impl
        ((sourceNodeRootTable env root)[recipe.2]?.join.getD [])

theorem RecipeMetadataProjects.restrict {env : PEnv} {root : DemandNode}
    {func : GIR.Func} {before after : LS}
    (projects : RecipeMetadataProjects env root func after)
    (retained : ∀ recipe ∈ before.valueRootRecipes, recipe ∈ after.valueRootRecipes) :
    RecipeMetadataProjects env root func before := by
  intro recipe member roots row
  exact projects recipe (retained recipe member) roots row

theorem lowerContextAt_recipeMetadataProjects (module : Core.Module) (ctx : Context) (impl : Impl) :
    RecipeMetadataProjects ⟨module, impl, ctx, []⟩ (.block impl.body)
      (lowerContextAt module ctx impl) (lowerImplState module impl) := by
  intro recipe member roots row
  exact lowerValueRootRows_exact ⟨module, impl, ctx, []⟩ _ _
    (lowerImplState_recipes module impl).1 member row

theorem lowerGlobal_recipeMetadataProjects (module : Core.Module) (global : Core.Global) :
    RecipeMetadataProjects ⟨module, initImpl, initContext, []⟩ (.expression global.init)
      (lowerGlobal module global).init (globalRecipeState module global) := by
  intro recipe member roots row
  exact lowerValueRootRows_exact ⟨module, initImpl, initContext, []⟩ _ _
    (globalRecipeState_recipes module global).1 member row

end Goose.Lower.Validation.SourceCanonicalRootFloors
