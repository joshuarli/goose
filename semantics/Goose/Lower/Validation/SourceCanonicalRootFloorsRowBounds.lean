import Goose.Lower.Validation.SourceCanonicalRootFloorsMetadata
import Goose.Core.Sound.Invert

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound

theorem lowerValueRootCeiling_refSliceVar_bounds (env : PEnv) (varId : VarId)
    (annotation : ∀ root ∈ (env.ann varId).getD [],
      match root with
      | .local index => index < env.impl.vars.size
      | .global index => index < env.mod.globals.size
      | .param index => index < env.impl.params.size) :
    ∀ root ∈ lowerValueRootCeiling env #[] (.refSliceVar varId),
      match root with
      | .local index => index < env.impl.vars.size
      | .global index => index < env.mod.globals.size
      | .param index => index < env.impl.params.size := by
  intro root member
  rcases unionRoots_mem _ _ _ member with declared | added
  · exact annotation root declared
  · cases located : env.impl.params[varId]? with
    | none => simp [located] at added
    | some parameter =>
      have inside := (Array.getElem?_eq_some_iff.mp located).1
      by_cases aligned : parameter.var = varId
      · simp only [located, Option.any_some, aligned, beq_self_eq_true, ite_true,
          List.mem_singleton] at added
        subst root
        exact inside
      · simp [located, aligned] at added

end Goose.Lower.Validation.SourceCanonicalRootFloors
