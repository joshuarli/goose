import Goose.Lower.Frag

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR

theorem recordValueRootRecipe_member {env : LEnv} {before after : LS}
    {value : ValueId} {scope : ScopeId} {result : Unit} {type : Ty}
    (run : recordValueRootRecipe value scope env before = (result, after))
    (live : after.cur.isSome = true)
    (typed : after.vals[value]? = some (some (.data type))) (refLike : type.isRefLike = true) :
    (value, .conditionalScope scope) ∈ after.valueRootRecipes := by
  rw [recordValueRootRecipe_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  simpa only [typed, Option.join_some, live, refLike, Bool.and_self, ite_true] using
    (Array.mem_push.mpr (Or.inr rfl) :
      (value, ValueRootSource.conditionalScope scope) ∈
        before.valueRootRecipes.push (value, .conditionalScope scope))

theorem lowerExpr_ifE_recipe {env : LEnv} {before after : LS}
    {condition : Expr} {yes no : Core.Block} {value : ValueId} {type : Ty}
    (run : lowerExpr (.ifE condition yes no) env before = (value, after))
    (live : after.cur.isSome = true)
    (typed : after.vals[value]? = some (some (.data type))) (refLike : type.isRefLike = true) :
    (value, .conditionalScope (sourceBlockScope yes)) ∈ after.valueRootRecipes := by
  obtain ⟨conditionValue, tested, _, remaining⟩ := bind_eq.mp run
  cases current : tested.cur with
  | none =>
      rw [whenLive_none _ _ env current] at remaining
      obtain ⟨_, rfl⟩ := Prod.mk.inj remaining
      simp [current] at live
  | some block =>
      rw [whenLive_some _ _ env current] at remaining
      obtain ⟨⟨left, right⟩, forked, _, _, selectedYes, _,
        yesValue, yesEnd, _, endYes, savedYes, _, _, selectedNo, _,
        noValue, noEnd, _, endNo, savedNo, _, joinedValue, joined, _,
        _, recorded, recipeRun, outputRun⟩ :=
        (by simpa only [bind_eq] using remaining)
      obtain ⟨rfl, rfl⟩ := pure_eq.mp outputRun
      exact recordValueRootRecipe_member recipeRun live typed refLike

end Goose.Lower.Validation.SourceCanonicalRootFloors
