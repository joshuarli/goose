import Goose.Lower.Frag

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem recordReadValueRootRecipe_tables (value : ValueId) (place : Place) (env : LEnv) (state : LS) :
    (recordReadValueRootRecipe value place env state).2.blocks = state.blocks ∧
    (recordReadValueRootRecipe value place env state).2.vals = state.vals ∧
    (recordReadValueRootRecipe value place env state).2.cur = state.cur := by
  cases place <;> simp [recordReadValueRootRecipe_run, recordValueRootSource_run] <;>
    split <;> exact ⟨rfl, rfl, rfl⟩

#print axioms recordReadValueRootRecipe_tables

end Goose.Lower.Validation
