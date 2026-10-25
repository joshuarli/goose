import Goose.Lower.Validation.SourceValueRecipeTypesBuilders

namespace Goose.Lower.Validation.SourceValueRecipeTypes

open Goose.Core Goose.GIR

theorem recipeTypes_recordValueRootSource (value : ValueId) (source : ValueRootSource) :
    RecipeTypeRun (recordValueRootSource value source) := by
  intro le before result after run checked
  let allowed := before.cur.isSome && (match before.vals[value]?.join with
    | some (.data type) => type.isRefLike
    | some (.view ..) => true
    | none => false)
  change ((), if allowed then
    { before with valueRootRecipes := before.valueRootRecipes.push (value, source) }
    else before) = (result, after) at run
  cases guard : allowed
  · simp only [guard, Bool.false_eq_true, ite_false] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨checked, .refl before⟩
  · simp only [guard, ite_true] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    refine ⟨?_, .refl before⟩
    intro recipe member
    rcases List.mem_append.mp (by simpa only [Array.toList_push] using member) with old | fresh
    · exact checked recipe old
    · have same := List.mem_singleton.mp fresh
      subst recipe
      have reference := (Bool.and_eq_true_iff.mp guard).2
      cases row : before.vals[value]? with
      | none => simp [row] at reference
      | some entry =>
        cases entry with
        | none => simp [row] at reference
        | some type =>
          refine ⟨type, rfl, ?_⟩
          cases type <;> simpa [row, VTy.refLike] using reference

theorem recipeTypes_recordValueRootRecipe (value : ValueId) (scope : ScopeId) :
    RecipeTypeRun (recordValueRootRecipe value scope) :=
  recipeTypes_recordValueRootSource value (.conditionalScope scope)

theorem recipeTypes_recordReadValueRootRecipe (value : ValueId) (place : Place) :
    RecipeTypeRun (recordReadValueRootRecipe value place) := by
  unfold recordReadValueRootRecipe
  cases place <;> first
    | exact RecipeTypeRun.pure ()
    | (refine RecipeTypeRun.bind recipeTypes_read fun le => ?_
       split
       · exact recipeTypes_recordValueRootSource value _
       · exact RecipeTypeRun.pure ())

theorem recipeTypes_joinValue (endT : Option BlockId) (vt : ValueId)
    (endF : Option BlockId) (vf : ValueId) :
    RecipeTypeRun (joinValue endT vt endF vf) := by
  unfold joinValue
  cases endT <;> cases endF
  · exact RecipeTypeRun.bind (recipeTypes_setCur _) fun _ => RecipeTypeRun.pure _
  all_goals
    exact RecipeTypeRun.bind (recipeTypes_valTy _) fun type =>
      RecipeTypeRun.bind (recipeTypes_newBlock [type]) fun pair =>
      RecipeTypeRun.bind (recipeTypes_patchBrs _ _) fun _ =>
      RecipeTypeRun.bind (recipeTypes_setCur _) fun _ => RecipeTypeRun.pure _

theorem recipeTypes_joinValue_record (endT : Option BlockId) (vt : ValueId)
    (endF : Option BlockId) (vf : ValueId) (scope : ScopeId) :
    RecipeTypeRun (do
      let value ← joinValue endT vt endF vf
      recordValueRootRecipe value scope
      pure value) := by
  exact RecipeTypeRun.bind (recipeTypes_joinValue endT vt endF vf) fun value =>
    RecipeTypeRun.bind (recipeTypes_recordValueRootRecipe value scope) fun _ => RecipeTypeRun.pure value

end Goose.Lower.Validation.SourceValueRecipeTypes
