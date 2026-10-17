import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSites
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

theorem occurrenceLedger_recordValueRootRecipe {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} (value : ValueId) (scope : ScopeId) :
    EmitsOnlyRun (InstructionOccurrences env root func types upper) (recordValueRootRecipe value scope) := by
  intro le before result after run
  apply EmitsOnly.of_blocks
  rw [recordValueRootRecipe_run] at run
  cases run
  rfl

theorem OccurrenceSitesBuilder.recordValueRootRecipe {env : PEnv} {root : DemandNode}
    {targets : List BlockId} {le : LEnv} {state : LS} {func : Func}
    {types : Array (Option VTy)} {upper : Prov}
    (sites : OccurrenceSitesBuilder env root targets le state func types upper)
    (value : ValueId) (scope : ScopeId) :
    OccurrenceSitesBuilder env root targets le (Goose.Lower.recordValueRootRecipe value scope le state).2
      func types upper := by
  have blocks : (Goose.Lower.recordValueRootRecipe value scope le state).2.blocks = state.blocks := by
    rw [recordValueRootRecipe_run]
  have values : (Goose.Lower.recordValueRootRecipe value scope le state).2.vals = state.vals := by
    rw [recordValueRootRecipe_run]
  exact sites.of_emits (.of_blocks blocks) (by intro value type row; simpa only [values] using row)
    (.of_blocks blocks) (Nat.le_refl _) (fun _ _ => rfl)

theorem recipesUnchangedB_assertCore (condition : ValueId) (origin : OriginId) :
    RecipesUnchangedB (whenLive () fun _ => do
      let (success, failure) ← fork condition
      Goose.Lower.setCur (some failure)
      Goose.Lower.emitTerm (.abort .assert (some origin))
      Goose.Lower.setCur (some success)) := by
  apply recipesUnchangedB_whenLive ()
  intro block
  apply RecipesUnchangedB.bind (recipesUnchangedB_fork condition)
  rintro ⟨success, failure⟩
  exact RecipesUnchangedB.bind (recipesUnchangedB_setCur (some failure)) fun _ =>
    RecipesUnchangedB.bind (recipesUnchangedB_emitTerm (.abort .assert (some origin))) fun _ =>
      recipesUnchangedB_setCur (some success)

#print axioms recipesUnchangedB_assertCore
#print axioms occurrenceLedger_recordValueRootRecipe
#print axioms OccurrenceSitesBuilder.recordValueRootRecipe

end Goose.Lower.Validation.ReplacementContentFlowSource
