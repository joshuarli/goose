import Goose.Lower.CoreToGir

set_option Elab.async false

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR

private theorem keyed_row_unique (rows : List (ValueId × ScopeId))
    (keys : (rows.map Prod.fst).Nodup) {first second : ValueId × ScopeId}
    (firstMember : first ∈ rows) (secondMember : second ∈ rows) (same : first.1 = second.1) :
    first = second := by
  induction rows with
  | nil => cases firstMember
  | cons head rest ih =>
      obtain ⟨absent, restKeys⟩ := List.nodup_cons.mp (by simpa only [List.map_cons] using keys)
      rcases List.mem_cons.mp firstMember with firstHead | firstRest
      · rcases List.mem_cons.mp secondMember with secondHead | secondRest
        · exact firstHead.trans secondHead.symm
        · have keyEq : second.1 = head.1 := same.symm.trans (congrArg Prod.fst firstHead)
          exact False.elim (absent (List.mem_map.mpr ⟨second, secondRest, keyEq⟩))
      · rcases List.mem_cons.mp secondMember with secondHead | secondRest
        · have keyEq : first.1 = head.1 := same.trans (congrArg Prod.fst secondHead)
          exact False.elim (absent (List.mem_map.mpr ⟨first, firstRest, keyEq⟩))
        · exact ih restKeys firstRest secondRest

theorem lowerValueRootRows_source (env : PEnv) (table : SourceRootTable)
    (recipes : Array (ValueId × ScopeId)) {value : ValueId} {roots : List RootRef}
    (row : (value, roots) ∈ (lowerValueRootRows env table recipes).getD #[]) :
    ∃ scope, (value, scope) ∈ recipes ∧
      roots = lowerContextRootCeiling env.ctx env.impl (table[scope]?.join.getD []) := by
  unfold lowerValueRootRows at row
  split at row
  · simp at row
  · obtain ⟨⟨id, scope⟩, member, equal⟩ := Array.mem_map.mp row
    have same := congrArg Prod.fst equal
    dsimp only at same
    subst id
    exact ⟨scope, member, (congrArg Prod.snd equal).symm⟩

theorem lowerValueRootRows_exact (env : PEnv) (table : SourceRootTable)
    (recipes : Array (ValueId × ScopeId)) (keys : (recipes.toList.map Prod.fst).Nodup)
    {value : ValueId} {scope : ScopeId} (recipe : (value, scope) ∈ recipes)
    {roots : List RootRef}
    (row : (value, roots) ∈ (lowerValueRootRows env table recipes).getD #[]) :
    roots = lowerContextRootCeiling env.ctx env.impl (table[scope]?.join.getD []) := by
  obtain ⟨foundScope, found, shape⟩ := lowerValueRootRows_source env table recipes row
  have same := keyed_row_unique recipes.toList keys (Array.mem_toList_iff.mpr found)
    (Array.mem_toList_iff.mpr recipe) rfl
  have scopeEq := congrArg Prod.snd same
  change foundScope = scope at scopeEq
  exact scopeEq ▸ shape

end Goose.Lower.Validation.SourceCanonicalRootFloors
