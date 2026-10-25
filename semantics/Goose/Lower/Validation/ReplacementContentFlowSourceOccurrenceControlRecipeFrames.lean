import Goose.Lower.Frag
import Goose.GIR.Effects
import Goose.Lower.Validation.SourceCanonicalRootFloorsMetadata

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

theorem recordValueRootRecipe_recorded_reference {value : ValueId} {scope : ScopeId}
    {le : LEnv} {state : LS}
    (recorded : (Goose.Lower.recordValueRootRecipe value scope le state).2.valueRootRecipes =
      state.valueRootRecipes.push (value, .conditionalScope scope)) :
    state.cur.isSome = true ∧ ∃ actual, state.vals[value]? = some (some actual) ∧ actual.refLike = true := by
  rw [recordValueRootRecipe_run] at recorded
  have active : (state.cur.isSome && (match state.vals[value]?.join with
      | some (.data type) => type.isRefLike
      | some (.view ..) => true
      | none => false)) = true := by
    by_cases enabled : (state.cur.isSome && (match state.vals[value]?.join with
        | some (.data type) => type.isRefLike
        | some (.view ..) => true
        | none => false)) = true
    · exact enabled
    · have unchanged : (Goose.Lower.recordValueRootRecipe value scope le state).2.valueRootRecipes =
          state.valueRootRecipes := by
        rw [recordValueRootRecipe_run]
        exact ite_eq_right enabled
      have original := recorded
      rw [← recordValueRootRecipe_run] at original
      have sizes := congrArg Array.size (unchanged.symm.trans original)
      simp at sizes
  obtain ⟨live, reference⟩ := Bool.and_eq_true_iff.mp active
  refine ⟨live, ?_⟩
  cases row : state.vals[value]? with
  | none => simp [row] at reference
  | some cell =>
    cases cell with
    | none => simp [row] at reference
    | some actual =>
      refine ⟨actual, rfl, ?_⟩
      cases actual <;> simpa [row, VTy.refLike] using reference

#print axioms recordValueRootRecipe_recorded_reference

end Goose.Lower.Validation.ReplacementContentFlowSource

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR

theorem RecipeMetadataProjects.of_prefix {env : PEnv} {root : DemandNode} {func : GIR.Func}
    {before after : LS} (projects : RecipeMetadataProjects env root func after)
    (initialRecipes : ∃ suffix, after.valueRootRecipes.toList = before.valueRootRecipes.toList ++ suffix) :
    RecipeMetadataProjects env root func before := by
  apply projects.restrict
  obtain ⟨suffix, same⟩ := initialRecipes
  intro recipe member
  apply Array.mem_toList_iff.mp
  rw [same]
  exact List.mem_append_left _ (Array.mem_toList_iff.mpr member)

theorem RecipeMetadataProjects.of_advance {env : PEnv} {root : DemandNode} {func : GIR.Func}
    {before after : LS} (projects : RecipeMetadataProjects env root func after)
    (advance : before.Adv after) : RecipeMetadataProjects env root func before :=
  projects.of_prefix advance.recipePrefix

#print axioms RecipeMetadataProjects.of_advance

end Goose.Lower.Validation.SourceCanonicalRootFloors
