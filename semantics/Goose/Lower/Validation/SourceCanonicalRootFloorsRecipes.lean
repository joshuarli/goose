import Goose.Lower.Validation.SourceCanonicalRootFloorsRecipesSource

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR

theorem recipes_initState : RecipesValid initState := by
  simp [RecipesValid, initState]

theorem lowerImplState_recipes (module : Core.Module) (impl : Impl) :
    RecipesValid (lowerImplState module impl) := by
  let action : B Unit := do
    let (entry, params) ← newBlock (impl.params.toList.map fun param => .data (tyOfVar impl param.var))
    setCur (some entry)
    let pre := (impl.params.toList.zip params).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  have preservation : RecipeRun action :=
    RecipeRun.bind (recipes_newBlock _) fun ⟨_, _⟩ =>
      RecipeRun.bind (recipes_setCur _) fun _ =>
      RecipeRun.bind (recipes_lowerBlock _ _ _ _) fun _ => recipes_finishFunction _ _
  exact (preservation (lowerEnv module impl.vars impl.results.toList) initState _ _ rfl recipes_initState).1

def globalRecipeState (module : Core.Module) (global : Core.Global) : LS :=
  let action : B Unit := do
    let (entry, _) ← newBlock []
    setCur (some entry)
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  (action (lowerEnv module #[] [global.ty]) initState).2

theorem globalRecipeState_recipes (module : Core.Module) (global : Core.Global) :
    RecipesValid (globalRecipeState module global) := by
  let action : B Unit := do
    let (entry, _) ← newBlock []
    setCur (some entry)
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  have preservation : RecipeRun action :=
    RecipeRun.bind (recipes_newBlock _) fun ⟨_, _⟩ =>
      RecipeRun.bind (recipes_setCur _) fun _ =>
      RecipeRun.bind (recipes_lowerExpr _) fun _ => recipes_emitTerm _
  exact (preservation (lowerEnv module #[] [global.ty]) initState _ _ rfl recipes_initState).1

theorem lowerValueRootRows_keys (env : PEnv) (table : SourceRootTable)
    (recipes : Array (ValueId × ScopeId)) :
    ((lowerValueRootRows env table recipes).getD #[]).toList.map Prod.fst =
      recipes.toList.map Prod.fst := by
  unfold lowerValueRootRows
  split
  · rename_i empty
    have same : recipes = #[] := Array.isEmpty_iff.mp empty
    simp [same]
  · simp [List.map_map, Function.comp_def]

theorem lowerValueRootRows_key_nodup {state : LS} (checked : RecipesValid state)
    (env : PEnv) (table : SourceRootTable) :
    (((lowerValueRootRows env table state.valueRootRecipes).getD #[]).toList.map Prod.fst).Nodup := by
  rw [lowerValueRootRows_keys]
  exact checked.1

theorem lowerValueRootRows_key_bound {state : LS} (checked : RecipesValid state)
    (env : PEnv) (table : SourceRootTable) {row : ValueId × List RootRef}
    (member : row ∈ ((lowerValueRootRows env table state.valueRootRecipes).getD #[]).toList) :
    row.1 < state.vals.size := by
  have key : row.1 ∈ state.valueRootRecipes.toList.map Prod.fst := by
    rw [← lowerValueRootRows_keys env table]
    exact List.mem_map.mpr ⟨row, member, rfl⟩
  obtain ⟨recipe, source, same⟩ := List.mem_map.mp key
  rw [← same]
  exact checked.2 recipe source

theorem lowerContextAt_valueRootKeys (module : Core.Module) (ctx : Context) (impl : Impl) :
    (((lowerContextAt module ctx impl).roots.values.getD #[]).toList.map Prod.fst).Nodup := by
  exact lowerValueRootRows_key_nodup (lowerImplState_recipes module impl) _ _

theorem lowerContextAt_valueRoots_bound (module : Core.Module) (ctx : Context) (impl : Impl)
    {row : ValueId × List RootRef}
    (member : row ∈ ((lowerContextAt module ctx impl).roots.values.getD #[]).toList) :
    row.1 < (lowerImplState module impl).vals.size :=
  lowerValueRootRows_key_bound (lowerImplState_recipes module impl) _ _ member

theorem lowerContextAt_valueRoots_numValues (module : Core.Module) (ctx : Context) (impl : Impl)
    (size : (lowerImplState module impl).vals.size = (lowerContextAt module ctx impl).numValues)
    {row : ValueId × List RootRef}
    (member : row ∈ ((lowerContextAt module ctx impl).roots.values.getD #[]).toList) :
    row.1 < (lowerContextAt module ctx impl).numValues := by
  rw [← size]
  exact lowerContextAt_valueRoots_bound module ctx impl member

theorem lowerGlobal_valueRootKeys (module : Core.Module) (global : Core.Global) :
    ((((lowerGlobal module global).init.roots.values.getD #[]).toList.map Prod.fst)).Nodup := by
  exact lowerValueRootRows_key_nodup (globalRecipeState_recipes module global) _ _

theorem lowerGlobal_valueRoots_bound (module : Core.Module) (global : Core.Global)
    {row : ValueId × List RootRef}
    (member : row ∈ ((lowerGlobal module global).init.roots.values.getD #[]).toList) :
    row.1 < (globalRecipeState module global).vals.size :=
  lowerValueRootRows_key_bound (globalRecipeState_recipes module global) _ _ member

theorem lowerGlobal_valueRoots_numValues (module : Core.Module) (global : Core.Global)
    (size : (globalRecipeState module global).vals.size = (lowerGlobal module global).init.numValues)
    {row : ValueId × List RootRef}
    (member : row ∈ ((lowerGlobal module global).init.roots.values.getD #[]).toList) :
    row.1 < (lowerGlobal module global).init.numValues := by
  rw [← size]
  exact lowerGlobal_valueRoots_bound module global member

#print axioms lowerImplState_recipes
#print axioms globalRecipeState_recipes
#print axioms lowerValueRootRows_keys
#print axioms lowerContextAt_valueRootKeys
#print axioms lowerContextAt_valueRoots_bound
#print axioms lowerGlobal_valueRootKeys
#print axioms lowerGlobal_valueRoots_bound

end Goose.Lower.Validation.SourceCanonicalRootFloors
