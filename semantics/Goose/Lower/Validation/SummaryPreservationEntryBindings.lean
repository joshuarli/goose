import Goose.Lower.Validation.SummaryPreservationSourceContextEnvironment
import Goose.Lower.Validation.SummaryPreservationEntrySeeds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem annotation_find_of_reference {module : Core.Module} {ctx : Context} {impl : Impl}
    {index : VarId} {localVar : LocalVar}
    (checked : checkAnnotationShape module impl ctx = .ok ())
    (variableRow : impl.vars[index]? = some localVar) (reference : localVar.ty.isRefLike = true) :
    ∃ annotation, (ctx.varRoots.find? (·.1 == index)).map (·.2) = some annotation := by
  cases found : ctx.varRoots.find? (·.1 == index) with
  | some row => exact ⟨row.2, rfl⟩
  | none =>
    have empty : ctx.varRoots.filter (·.1 == index) = [] :=
      List.filter_eq_nil_iff.mpr (List.find?_eq_none.mp found)
    have count := (Core.Declarative.annotations_sound module impl ctx checked).2.1 index localVar variableRow reference
    rw [empty] at count
    cases count

theorem entry_parameter_roots_within_slots {module : Core.Module} {ctx : Context} {impl : Impl}
    {index : Nat} {param : Param} {localVar : LocalVar}
    (checked : CtxOk module impl ctx)
    (parameterRow : impl.params[index]? = some param) (identity : param.var = index)
    (variableRow : impl.vars[index]? = some localVar) :
    ∀ root ∈ rootsAt (entryRootValues (impl.params.toList.map fun p => .data (tyOfVar impl p.var))) index,
      root ∈ rootsAt (typedContextSlotUpper module ctx impl) param.var := by
  have typeAt : (impl.params.toList.map fun p => VTy.data (tyOfVar impl p.var))[index]? =
      some (.data localVar.ty) := by
    rw [List.getElem?_map, Array.getElem?_toList, parameterRow]
    simp only [Option.map_some, identity, tyOfVar, variableRow, Option.map_some]
  rw [entryRootValues_at typeAt]
  by_cases reference : localVar.ty.isRefLike = true
  · simp only [VTy.refLike, reference, ↓reduceIte]
    intro root member
    have same := List.mem_singleton.mp member
    subst root
    obtain ⟨annotation, annotationAt⟩ := annotation_find_of_reference checked.annotationShape variableRow reference
    rw [identity]
    exact typedContextSlotUpper_parameter parameterRow identity variableRow annotationAt
  · have scalar : (VTy.data localVar.ty).refLike = false := Bool.eq_false_iff.mpr reference
    simp only [scalar, Bool.false_eq_true, ite_false]
    simp

#print axioms annotation_find_of_reference
#print axioms entry_parameter_roots_within_slots

end Goose.Lower.Validation.SummaryPreservation
