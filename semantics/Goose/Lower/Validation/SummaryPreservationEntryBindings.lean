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

theorem checkImpl_variable_origin_bound {module : Core.Module} {impl : Impl}
    {index : VarId} {localVar : LocalVar} (checked : checkImpl module impl = .ok ())
    (variableRow : impl.vars[index]? = some localVar) : localVar.org < module.origins.size := by
  unfold checkImpl at checked
  by_cases several : impl.results.size > 1
  · simp [several, chk] at checked
  · simp only [several] at checked
    obtain ⟨_, _, checked⟩ := (ex_bind_ok _ _ _).mp checked
    obtain ⟨_, _, checked⟩ := (ex_bind_ok _ _ _).mp checked
    obtain ⟨_, _, checked⟩ := (ex_bind_ok _ _ _).mp checked
    obtain ⟨_, origins, _⟩ := (ex_bind_ok _ _ _).mp checked
    have one := (forAll_ok _ _).mp origins localVar
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? variableRow))
    by_cases bound : localVar.org < module.origins.size
    · exact bound
    · simp [bound, chk] at one

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

theorem entry_parameter_pair {module : Core.Module} {impl : Impl} {implementation : ImplId}
    {param : Param} {value : ValueId} (le : LEnv)
    (accepted : Core.validate module = .ok ())
    (implementationRow : module.impls[implementation]? = some impl)
    (paired : (param, value) ∈ impl.params.toList.zip
      (newBlock (impl.params.toList.map fun p => VTy.data (tyOfVar impl p.var)) le initState).1.2) :
    ∃ index localVar, impl.params[index]? = some param ∧ param.var = index ∧ value = index ∧
      impl.vars[index]? = some localVar ∧ localVar.org < module.origins.size := by
  obtain ⟨index, pairAt⟩ := List.mem_iff_getElem?.mp paired
  obtain ⟨parameterAt, valueAt⟩ := List.getElem?_zip_eq_some.mp pairAt
  have row : impl.params[index]? = some param := by simpa only [Array.getElem?_toList] using parameterAt
  have bound : index < impl.params.size := (Array.getElem?_eq_some_iff.mp row).1
  have ids : (newBlock (impl.params.toList.map fun p => VTy.data (tyOfVar impl p.var)) le initState).1.2 =
      List.range impl.params.size := by simp [newBlock_run_general, paramIds, initState]
  rw [ids, List.getElem?_range bound] at valueAt
  obtain ⟨identity, localVar, variableRow, _, _⟩ := (validate_modOk module accepted).impl implementation impl implementationRow
    |>.params index param row
  exact ⟨index, localVar, row, identity, (Option.some.inj valueAt).symm, variableRow,
    checkImpl_variable_origin_bound (accepted_implementation_checked accepted implementationRow) variableRow⟩

#print axioms entry_parameter_pair

#print axioms checkImpl_variable_origin_bound
#print axioms annotation_find_of_reference
#print axioms entry_parameter_roots_within_slots

end Goose.Lower.Validation.SummaryPreservation
