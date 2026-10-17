import Goose.Lower.CoreToGir

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR

def RecipesValid (state : LS) : Prop :=
  (state.valueRootRecipes.toList.map Prod.fst).Nodup ∧
    ∀ recipe ∈ state.valueRootRecipes.toList, recipe.1 < state.vals.size

def RecipeRun (action : B α) : Prop :=
  ∀ le before result after, action le before = (result, after) →
    RecipesValid before → RecipesValid after ∧ before.vals.size ≤ after.vals.size

@[simp] private theorem get_run (le : LEnv) (state : LS) : (get : B LS) le state = (state, state) := rfl

@[simp] private theorem read_run (le : LEnv) (state : LS) : (read : B LEnv) le state = (le, state) := rfl

private theorem bind_run (action : B α) (next : α → B β) (le : LEnv) (state : LS) :
    (action >>= next) le state = next (action le state).1 le (action le state).2 := rfl

private theorem pure_run (value : α) (le : LEnv) (state : LS) :
    (pure value : B α) le state = (value, state) := rfl

private theorem bind_eq {action : B α} {next : α → B β} {le : LEnv} {before after : LS} {result : β} :
    (action >>= next) le before = (result, after) ↔
      ∃ value middle, action le before = (value, middle) ∧ next value le middle = (result, after) := by
  constructor
  · intro run
    exact ⟨(action le before).1, (action le before).2, rfl, run⟩
  · rintro ⟨value, middle, first, last⟩
    simpa only [bind_run, first] using last

private theorem pure_eq {value result : α} {le : LEnv} {before after : LS} :
    (pure value : B α) le before = (result, after) ↔ value = result ∧ before = after := by
  change (value, before) = (result, after) ↔ _
  simp only [Prod.mk.injEq]

theorem RecipeRun.pure (value : α) : RecipeRun (pure value) := by
  intro le before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact ⟨checked, Nat.le_refl _⟩

theorem RecipeRun.bind {action : B α} {next : α → B β}
    (first : RecipeRun action) (second : ∀ value, RecipeRun (next value)) :
    RecipeRun (action >>= next) := by
  intro le before result after run checked
  obtain ⟨value, middle, firstRun, secondRun⟩ := bind_eq.mp run
  have one := first le before value middle firstRun checked
  have two := second value le middle result after secondRun one.1
  exact ⟨two.1, Nat.le_trans one.2 two.2⟩

theorem RecipeRun.of_frame {action : B α}
    (frame : ∀ le state, (action le state).2.valueRootRecipes = state.valueRootRecipes ∧
      state.vals.size ≤ (action le state).2.vals.size) : RecipeRun action := by
  intro le before result after run checked
  obtain ⟨same, grows⟩ := frame le before
  rw [run] at same grows
  change after.valueRootRecipes = before.valueRootRecipes at same
  change before.vals.size ≤ after.vals.size at grows
  refine ⟨⟨?_, ?_⟩, grows⟩
  · simpa only [same] using checked.1
  · intro recipe member
    rw [same] at member
    exact Nat.lt_of_lt_of_le (checked.2 recipe member) grows

theorem recipes_emitDef (op : Op) : RecipeRun (emitDef op) := by
  apply RecipeRun.of_frame
  intro le state
  cases current : state.cur <;>
    simp [emitDef, current, bind, pure, modify, modifyGet, MonadStateOf.modifyGet, pushInst]

private theorem fold_params_size (types : List VTy) (values : Array (Option VTy)) :
    (types.foldl (fun array type => array.push (some type)) values).size = values.size + types.length := by
  induction types generalizing values with
  | nil => simp
  | cons type rest ih => simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (values.push (some type))

theorem recipes_newBlock (types : List VTy) : RecipeRun (newBlock types) := by
  apply RecipeRun.of_frame
  intro le state
  change state.valueRootRecipes = state.valueRootRecipes ∧
    state.vals.size ≤ (types.foldl (fun array type => array.push (some type)) state.vals).size
  rw [fold_params_size]
  exact ⟨rfl, Nat.le_add_right _ _⟩

theorem recipes_emitEffect (effect : Effect) : RecipeRun (emitEffect effect) := by
  apply RecipeRun.of_frame
  intro le state
  cases current : state.cur <;>
    simp [emitEffect, curBlock, current, bind, pure, modify, modifyGet, MonadStateOf.modifyGet, pushInst]

theorem recipes_emitTerm (term : Term) : RecipeRun (emitTerm term) := by
  apply RecipeRun.of_frame
  intro le state
  cases current : state.cur <;>
    simp [emitTerm, curBlock, current, setCur, bind, pure, modify, modifyGet, MonadStateOf.modifyGet, pushInst]

theorem recipes_patchTerm (block : BlockId) (term : Term) : RecipeRun (patchTerm block term) := by
  apply RecipeRun.of_frame
  intros
  exact ⟨rfl, Nat.le_refl _⟩

theorem recipes_setCur (block : Option BlockId) : RecipeRun (setCur block) := by
  apply RecipeRun.of_frame
  intros
  exact ⟨rfl, Nat.le_refl _⟩

theorem recipes_curBlock : RecipeRun curBlock := by
  apply RecipeRun.of_frame
  intros
  exact ⟨rfl, Nat.le_refl _⟩

theorem recipes_get : RecipeRun (get : B LS) := by
  apply RecipeRun.of_frame
  intros
  exact ⟨rfl, Nat.le_refl _⟩

theorem recipes_read : RecipeRun (read : B LEnv) := by
  apply RecipeRun.of_frame
  intros
  exact ⟨rfl, Nat.le_refl _⟩

theorem recipes_valTy (value : ValueId) : RecipeRun (valTy value) := by
  apply RecipeRun.of_frame
  intro le state
  cases row : state.vals[value]? with
  | none => simp [valTy, bind, pure, row]
  | some type => cases type <;> simp [valTy, bind, pure, row]

theorem recipes_pushScope (scope : ScopeId) : RecipeRun (pushScope scope) := by
  apply RecipeRun.of_frame
  intros
  exact ⟨rfl, Nat.le_refl _⟩

theorem recipes_popScope : RecipeRun popScope := by
  apply RecipeRun.of_frame
  intros
  exact ⟨rfl, Nat.le_refl _⟩

#print axioms recipes_emitDef
#print axioms recipes_newBlock

end Goose.Lower.Validation.SourceCanonicalRootFloors
