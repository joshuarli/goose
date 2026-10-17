import Goose.Lower.Validation.SourceCanonicalFactsResultFloors
import Goose.Lower.ContextLowering
import Goose.Core.Sound.Module

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lower_canonical_resultFloor_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : FnId} {func : Func}
    (functionAt : (lower module).funcs[index]? = some func)
    (reference : (func.results[0]?).any Ty.isRefLike = true) :
    func.roots.results[0]?.getD [] ⊆ rootsAt (GIR.resultRoots (lower module) (lower module).implTypes) index := by
  cases contextAt : module.contexts[index]? with
  | none => simp [lower, Array.getElem?_map, contextAt] at functionAt
  | some context =>
    obtain ⟨impl, implAt, _⟩ := (validate_modOk module accepted).ctx index context contextAt
    have lowered := lower_func_at contextAt implAt
    have same : func = lowerContextAt module context impl := Option.some.inj (functionAt.symm.trans lowered)
    subst func
    obtain ⟨bodyTy, finish, typed, resultShape⟩ := ((validate_modOk module accepted).impl context.impl impl implAt).body
    rcases resultShape with ⟨empty, _⟩ | ⟨type, singleton, _⟩
    · change ((impl.results.toList)[0]?).any Ty.isRefLike = true at reference
      simp [empty] at reference
    · have resultType : (lowerContextAt module context impl).results = [type] := singleton
      have referenceType : type.isRefLike = true := by simpa only [resultType, List.getElem?_cons_zero, Option.any_some] using reference
      have schema : (lowerContextAt module context impl).roots.slots.isSome = true := rfl
      have startRow : rootsAt (lower module).declaredResultRoots index =
          (lowerContextAt module context impl).roots.results[0]?.getD [] := by
        simp only [rootsAt, GIR.Module.declaredResultRoots, Array.getElem?_map, lowered, Option.map_some, Option.getD_some,
          resultType, schema, referenceType, Bool.and_self, ite_true]
      intro root member
      apply native_declared_resultRoots_retained (lower module) (lower module).implTypes
        (by simp [GIR.Module.implTypes, GIR.Module.infos, GIR.Module.labelled]) lowered root
      rw [startRow]
      exact member

#print axioms lower_canonical_resultFloor_of_accepted

end Goose.Lower.Validation
