import Goose.Lower.Validation.ValueTypes
import Goose.GIR.Effects

namespace Goose.Lower.Validation.SourceValueRecipeTypes

open Goose.Core Goose.GIR

def RecipesTyped (state : LS) : Prop :=
  ∀ recipe ∈ state.valueRootRecipes.toList,
    ∃ type, state.vals[recipe.1]? = some (some type) ∧ type.refLike = true

def RecipeTypeRun (action : B α) : Prop :=
  ∀ le before result after, action le before = (result, after) →
    RecipesTyped before → RecipesTyped after ∧ TypePrefix before after

theorem RecipesTyped.retained {before after : LS} (checked : RecipesTyped before)
    (same : after.valueRootRecipes = before.valueRootRecipes)
    (typed : TypePrefix before after) : RecipesTyped after := by
  intro recipe member
  rw [same] at member
  obtain ⟨type, row, reference⟩ := checked recipe member
  exact ⟨type, typed _ _ row, reference⟩

theorem RecipeTypeRun.pure (value : α) : RecipeTypeRun (pure value) := by
  intro le before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact ⟨checked, .refl before⟩

theorem RecipeTypeRun.bind {action : B α} {next : α → B β}
    (first : RecipeTypeRun action) (second : ∀ value, RecipeTypeRun (next value)) :
    RecipeTypeRun (action >>= next) := by
  intro le before result after run checked
  obtain ⟨value, middle, firstRun, secondRun⟩ := bind_eq.mp run
  have one := first le before value middle firstRun checked
  have two := second value le middle result after secondRun one.1
  exact ⟨two.1, one.2.trans two.2⟩

theorem RecipeTypeRun.of_frame {action : B α}
    (same : RecipesUnchangedB action) (typed : TypeRun action) : RecipeTypeRun action := by
  intro le before result after run checked
  have frame := same le before
  rw [run] at frame
  have preserved := typed le before result after run
  exact ⟨checked.retained frame preserved, preserved⟩

theorem recipeTypes_emitDef (op : Op) : RecipeTypeRun (emitDef op) :=
  .of_frame (recipesUnchangedB_emitDef op) (types_emitDef op)

theorem recipeTypes_newBlock (types : List VTy) : RecipeTypeRun (newBlock types) :=
  .of_frame (recipesUnchangedB_newBlock types) (types_newBlock types)

theorem recipeTypes_emitEffect (effect : Effect) : RecipeTypeRun (emitEffect effect) :=
  .of_frame (recipesUnchangedB_emitEffect effect) (types_emitEffect effect)

theorem recipeTypes_emitTerm (term : Term) : RecipeTypeRun (emitTerm term) :=
  .of_frame (recipesUnchangedB_emitTerm term) (types_emitTerm term)

theorem recipeTypes_patchTerm (block : BlockId) (term : Term) : RecipeTypeRun (patchTerm block term) :=
  .of_frame (recipesUnchangedB_patchTerm block term) (types_patchTerm block term)

theorem recipeTypes_setCur (block : Option BlockId) : RecipeTypeRun (setCur block) :=
  .of_frame (recipesUnchangedB_setCur block) (types_setCur block)

theorem recipeTypes_curBlock : RecipeTypeRun curBlock :=
  .of_frame (by intro le state; rw [curBlock_run]) types_curBlock

theorem recipeTypes_get : RecipeTypeRun (get : B LS) :=
  .of_frame recipesUnchangedB_get types_get

theorem recipeTypes_read : RecipeTypeRun (read : B LEnv) :=
  .of_frame recipesUnchangedB_read types_read

theorem recipeTypes_valTy (value : ValueId) : RecipeTypeRun (valTy value) :=
  .of_frame (recipesUnchangedB_valTy value) (types_valTy value)

theorem recipeTypes_pushScope (scope : ScopeId) : RecipeTypeRun (pushScope scope) :=
  .of_frame (recipesUnchangedB_pushScope scope) (types_pushScope scope)

theorem recipeTypes_popScope : RecipeTypeRun popScope :=
  .of_frame recipesUnchangedB_popScope types_popScope

end Goose.Lower.Validation.SourceValueRecipeTypes
