import Goose.Lower.Validation.SummaryPreservationSource

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound

theorem accepted_implementation_checked {module : Module} {index : ImplId} {impl : Impl}
    (accepted : validate module = .ok ()) (lookup : module.impls[index]? = some impl) :
    checkImpl module impl = .ok () := by
  unfold validate at accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, implementations, _⟩ := (ex_bind_ok _ _ _).mp accepted
  exact (forAll_ok _ _).mp implementations impl
    (List.mem_of_getElem? (by simpa using lookup))


theorem checkImpl_refSlice_parameter {module : Module} {impl : Impl} {index : Nat}
    {localVar : LocalVar} (checked : checkImpl module impl = .ok ())
    (variableRow : impl.vars[index]? = some localVar) (reference : localVar.ty.isRefSlice = true) :
    ∃ param, impl.params[index]? = some param ∧ param.var = index ∧ param.mode = .byRef := by
  have notStorable : localVar.ty.storable = false := by
    cases type : localVar.ty <;> simp_all [Ty.isRefSlice, Ty.storable]
    rename_i mutability target
    cases target <;> simp_all [Ty.isRefSlice, Ty.storable, Ty.refTarget]
  unfold checkImpl at checked
  cases scope : scopeOrderError (blockScopes none impl.body) 0 with
  | some message =>
    simp only [scope] at checked
    inv at checked
  | none =>
    simp only [scope] at checked
    inv at checked
    obtain ⟨_, _, _, variables, _, _, _, _, _, _, _⟩ := checked
    have row := (forAll_ok _ _).mp variables (localVar, index)
      (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using variableRow))
    inv at row
    simp only [notStorable, Bool.false_or, reference, Bool.true_and] at row
    cases parameter : impl.params[index]? with
    | none => simp [parameter] at row
    | some param =>
      simp only [parameter, Bool.and_eq_true, beq_iff_eq] at row
      exact ⟨param, rfl, row.1, row.2⟩


theorem accepted_refSlice_parameter {module : Module} {implementation : ImplId} {impl : Impl}
    {index : Nat} {localVar : LocalVar}
    (accepted : validate module = .ok ()) (lookup : module.impls[implementation]? = some impl)
    (variableRow : impl.vars[index]? = some localVar) (reference : localVar.ty.isRefSlice = true) :
    ∃ param, impl.params[index]? = some param ∧ param.var = index ∧ param.mode = .byRef :=
  checkImpl_refSlice_parameter (accepted_implementation_checked accepted lookup) variableRow reference

end Goose.Lower.Validation.SummaryPreservation
