import Goose.Lower.Frag

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR

theorem lowerExpr_readVar_recipe {env : LEnv} {before after : LS}
    {varId : VarId} {value : ValueId} {type : Ty}
    (run : lowerExpr (.read (.var varId)) env before = (value, after))
    (live : after.cur.isSome = true)
    (reference : (env.vars[varId]?).any (·.ty.isRefSlice) = true)
    (typed : after.vals[value]? = some (some (.data type))) (refLike : type.isRefLike = true) :
    (value, .refSliceVar varId) ∈ after.valueRootRecipes := by
  simp only [lowerExpr] at run
  obtain ⟨address, middle, _, run⟩ := bind_eq.mp run
  obtain ⟨loaded, emitted, _, run⟩ := bind_eq.mp run
  obtain ⟨recordResult, recorded, recordRun, run⟩ := bind_eq.mp run
  obtain ⟨rfl, rfl⟩ := pure_eq.mp run
  cases recordResult
  simp only [recordReadValueRootRecipe_run, reference, ite_true,
    recordValueRootSource_run] at recordRun
  obtain ⟨_, rfl⟩ := Prod.mk.inj recordRun
  simpa only [typed, Option.join_some, live, refLike, Bool.and_self, ite_true] using
    (Array.mem_push.mpr (Or.inr rfl) :
      (loaded, ValueRootSource.refSliceVar varId) ∈
        emitted.valueRootRecipes.push (loaded, .refSliceVar varId))

end Goose.Lower.Validation.SourceCanonicalRootFloors
