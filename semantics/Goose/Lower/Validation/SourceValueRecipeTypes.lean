import Goose.Lower.Validation.SourceValueRecipeTypesSource

namespace Goose.Lower.Validation.SourceValueRecipeTypes

open Goose.Core Goose.GIR

theorem recipeTypes_initState : RecipesTyped initState := by
  simp [RecipesTyped, initState]

theorem lowerImplState_recipeTypes (module : Core.Module) (impl : Impl) :
    RecipesTyped (lowerImplState module impl) := by
  let action : B Unit := do
    let (entry, params) ← newBlock (impl.params.toList.map fun param => .data (tyOfVar impl param.var))
    setCur (some entry)
    let pre := (impl.params.toList.zip params).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  have preservation : RecipeTypeRun action :=
    RecipeTypeRun.bind (recipeTypes_newBlock _) fun ⟨_, _⟩ =>
      RecipeTypeRun.bind (recipeTypes_setCur _) fun _ =>
      RecipeTypeRun.bind (recipeTypes_lowerBlock _ _ _ _) fun _ => recipeTypes_finishFunction _ _
  exact (preservation (lowerEnv module impl.vars impl.results.toList) initState _ _ rfl recipeTypes_initState).1

def globalRecipeTypeState (module : Core.Module) (global : Core.Global) : LS :=
  let action : B Unit := do
    let (entry, _) ← newBlock []
    setCur (some entry)
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  (action (lowerEnv module #[] [global.ty]) initState).2

theorem globalRecipeTypeState_recipeTypes (module : Core.Module) (global : Core.Global) :
    RecipesTyped (globalRecipeTypeState module global) := by
  let action : B Unit := do
    let (entry, _) ← newBlock []
    setCur (some entry)
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  have preservation : RecipeTypeRun action :=
    RecipeTypeRun.bind (recipeTypes_newBlock _) fun ⟨_, _⟩ =>
      RecipeTypeRun.bind (recipeTypes_setCur _) fun _ =>
      RecipeTypeRun.bind (recipeTypes_lowerExpr _) fun _ => recipeTypes_emitTerm _
  exact (preservation (lowerEnv module #[] [global.ty]) initState _ _ rfl recipeTypes_initState).1

theorem lowerValueRootRows_type {state : LS} (checked : RecipesTyped state)
    (env : PEnv) (table : SourceRootTable) {row : ValueId × List RootRef}
    (member : row ∈ ((lowerValueRootRows env table state.valueRootRecipes).getD #[]).toList) :
    ∃ type, state.vals[row.1]? = some (some type) ∧ type.refLike = true := by
  unfold lowerValueRootRows at member
  split at member
  · simp at member
  · simp only [Option.getD_some, Array.toList_map] at member
    obtain ⟨recipe, recipeMember, same⟩ := List.mem_map.mp member
    obtain ⟨type, typed, reference⟩ := checked recipe recipeMember
    refine ⟨type, ?_, reference⟩
    simpa only [← congrArg Prod.fst same] using typed

theorem lowerContextAt_valueRoots_type (module : Core.Module) (ctx : Context) (impl : Impl)
    {row : ValueId × List RootRef}
    (member : row ∈ ((lowerContextAt module ctx impl).roots.values.getD #[]).toList) :
    ∃ type, (lowerImplState module impl).vals[row.1]? = some (some type) ∧ type.refLike = true :=
  lowerValueRootRows_type (lowerImplState_recipeTypes module impl) _ _ member

theorem lowerGlobal_valueRoots_type (module : Core.Module) (global : Core.Global)
    {row : ValueId × List RootRef}
    (member : row ∈ ((lowerGlobal module global).init.roots.values.getD #[]).toList) :
    ∃ type, (globalRecipeTypeState module global).vals[row.1]? = some (some type) ∧ type.refLike = true :=
  lowerValueRootRows_type (globalRecipeTypeState_recipeTypes module global) _ _ member

end Goose.Lower.Validation.SourceValueRecipeTypes
