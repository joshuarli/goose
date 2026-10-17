import Goose.Lower.Validation.SourceCanonicalRootFloorsRecipesBuilders

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR

private theorem bind_run (action : B α) (next : α → B β) (le : LEnv) (state : LS) :
    (action >>= next) le state = next (action le state).1 le (action le state).2 := rfl

@[simp] private theorem get_run (le : LEnv) (state : LS) : (get : B LS) le state = (state, state) := rfl

@[simp] private theorem set_run (next : LS) (le : LEnv) (state : LS) : (set next : B Unit) le state = ((), next) := rfl

private def queriedType (value : ValueId) (state : LS) : VTy :=
  match state.vals[value]? with
  | some (some type) => type
  | _ => .data .unit

private theorem valTy_run (value : ValueId) (le : LEnv) (state : LS) :
    valTy value le state = (queriedType value state, state) := by
  cases row : state.vals[value]? with
  | none => simp [valTy, queriedType, bind, pure, row]
  | some type => cases type <;> simp [valTy, queriedType, bind, pure, row]

@[simp] theorem patchBrs_recipes (target : BlockId) : ∀ incoming le state,
    (patchBrs target incoming le state).2.valueRootRecipes = state.valueRootRecipes
  | [], le, state => rfl
  | (block, value) :: rest, le, state => by
    simpa [patchBrs, bind, pure, patchTerm, pushInst, modify, modifyGet, MonadStateOf.modifyGet] using patchBrs_recipes target rest le
      { state with blocks := state.blocks.modify block fun body => { body with insts := body.insts.push (.term (.br target [value])) } }

@[simp] theorem patchBrs_vals (target : BlockId) : ∀ incoming le state,
    (patchBrs target incoming le state).2.vals = state.vals
  | [], le, state => rfl
  | (block, value) :: rest, le, state => by
    simpa [patchBrs, bind, pure, patchTerm, pushInst, modify, modifyGet, MonadStateOf.modifyGet] using patchBrs_vals target rest le
      { state with blocks := state.blocks.modify block fun body => { body with insts := body.insts.push (.term (.br target [value])) } }

theorem joinValue_recipe_frame (endT : Option BlockId) (vt : ValueId)
    (endF : Option BlockId) (vf : ValueId) (le : LEnv) (before : LS) :
    let output := joinValue endT vt endF vf le before
    output.2.valueRootRecipes = before.valueRootRecipes ∧
      before.vals.size ≤ output.2.vals.size ∧
      (output.2.cur.isSome = true → output.1 = before.vals.size ∧ output.1 < output.2.vals.size) := by
  cases endT <;> cases endF <;>
    simp [joinValue, bind, valTy_run, newBlock, setCur, pure, modify,
      modifyGet, MonadStateOf.modifyGet]

theorem recipes_record_fresh {le : LEnv} {before after : LS} {result : Unit} {value : ValueId} {scope : ScopeId}
    (run : recordValueRootRecipe value scope le before = (result, after))
    (checked : RecipesValid before)
    (bounded : before.cur.isSome = true → value < before.vals.size)
    (fresh : before.cur.isSome = true → ∀ recipe ∈ before.valueRootRecipes.toList, recipe.1 ≠ value) :
    RecipesValid after ∧ before.vals.size ≤ after.vals.size := by
  let allowed := before.cur.isSome && (match before.vals[value]?.join with
    | some (.data type) => type.isRefLike
    | some (.view ..) => true
    | none => false)
  change ((), if allowed then
      { before with valueRootRecipes := before.valueRootRecipes.push (value, scope) }
    else before) = (result, after) at run
  cases guard : allowed
  · simp only [guard, Bool.false_eq_true, ite_false] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨checked, Nat.le_refl _⟩
  · simp only [guard, ite_true] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have live : before.cur.isSome = true := (Bool.and_eq_true_iff.mp guard).1
    refine ⟨⟨?_, ?_⟩, Nat.le_refl _⟩
    · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
      apply List.nodup_append.mpr
      refine ⟨checked.1, by simp, ?_⟩
      intro old oldMember next nextMember same
      have nextEq := List.mem_singleton.mp nextMember
      obtain ⟨recipe, member, rfl⟩ := List.mem_map.mp oldMember
      exact fresh live recipe member (same.trans nextEq)
    · intro recipe member
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact checked.2 recipe old
      · exact bounded live

theorem recipes_joinValue_record (endT : Option BlockId) (vt : ValueId)
    (endF : Option BlockId) (vf : ValueId) (scope : ScopeId) :
    RecipeRun (do
      let value ← joinValue endT vt endF vf
      recordValueRootRecipe value scope
      pure value) := by
  intro le before result after run checked
  let joined := joinValue endT vt endF vf le before
  have frame : joined.2.valueRootRecipes = before.valueRootRecipes ∧
      before.vals.size ≤ joined.2.vals.size ∧
      (joined.2.cur.isSome = true → joined.1 = before.vals.size ∧ joined.1 < joined.2.vals.size) :=
    joinValue_recipe_frame endT vt endF vf le before
  have joinedChecked : RecipesValid joined.2 := by
    refine ⟨?_, ?_⟩
    · simpa only [frame.1] using checked.1
    · intro recipe member
      rw [frame.1] at member
      exact Nat.lt_of_lt_of_le (checked.2 recipe member) frame.2.1
  have recordRun : recordValueRootRecipe joined.1 scope le joined.2 =
      ((), (recordValueRootRecipe joined.1 scope le joined.2).2) := by
    simp [recordValueRootRecipe, modify, modifyGet, MonadStateOf.modifyGet]
  have final := recipes_record_fresh recordRun joinedChecked (fun live => (frame.2.2 live).2) (by
    intro live recipe member same
    have old : recipe.1 < before.vals.size := checked.2 recipe (by simpa only [frame.1] using member)
    rw [same, (frame.2.2 live).1] at old
    exact Nat.lt_irrefl _ old)
  simp only [bind_run] at run
  change (joined.1, (recordValueRootRecipe joined.1 scope le joined.2).2) = (result, after) at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨final.1, Nat.le_trans frame.2.1 final.2⟩

#print axioms recipes_joinValue_record

end Goose.Lower.Validation.SourceCanonicalRootFloors
