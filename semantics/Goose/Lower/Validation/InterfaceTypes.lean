import Goose.Lower.Validation.ResolvedTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem validate_implementation_checks {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {impl : Core.Impl}
    (member : impl ∈ module.impls.toList) : Core.checkImpl module impl = .ok () := by
  unfold Core.validate at accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, implementations, _⟩ := (ex_bind_ok _ _ _).mp accepted
  exact (forAll_ok _ _).mp implementations impl member

theorem checkImpl_metadata_checks {module : Core.Module} {impl : Core.Impl}
    (checked : Core.checkImpl module impl = .ok ()) :
    (Core.forAll impl.results.toList fun ty =>
      unless ty.readable && ty != .unit do
        Core.reject .type s!"{impl.name} has a result of a type no function may return") = .ok () ∧
    (Core.forAll impl.vars.toList.zipIdx fun (localVar, index) =>
      unless localVar.ty.storable || (localVar.ty.isRefSlice && match impl.params[index]? with
        | some param => param.var == index && param.mode == .byRef
        | none => false) do
        Core.reject .type s!"{impl.name}: variable {localVar.name} has a type no variable may have") = .ok () := by
  unfold Core.checkImpl at checked
  by_cases several : impl.results.size > 1
  · simp [several, chk] at checked
  · simp only [several] at checked
    obtain ⟨_, results, checked⟩ := (ex_bind_ok _ _ _).mp checked
    obtain ⟨_, _, checked⟩ := (ex_bind_ok _ _ _).mp checked
    obtain ⟨_, locals, _⟩ := (ex_bind_ok _ _ _).mp checked
    exact ⟨results, locals⟩

theorem readable_noRefSlice {ty : Ty} (readable : ty.readable = true) : ty.isRefSlice = false := by
  cases ty with
  | ref mu target => cases target <;> simp_all [Ty.readable, Ty.refTarget, Ty.isRefSlice]
  | _ => rfl

theorem lowerImpl_resultTypeChecks {module : Core.Module} {index : ImplId} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ()) (lookup : module.impls[index]? = some impl) :
    (GIR.checkAll (lowerImpl module impl).results fun ty => do
      unless !ty.isRefSlice do throw "a reference-to-slice type is only valid for a parameter") =
      (Except.ok () : Except String Unit) := by
  apply Origins.checkAll_ok_of_forall
  intro ty member
  have checked := validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
  have one := (forAll_ok _ _).mp (checkImpl_metadata_checks checked).1 ty member
  have readable : ty.readable = true := by
    by_cases readable : ty.readable = true
    · exact readable
    · simp [readable, chk] at one
  simp [readable_noRefSlice readable, pure, Except.pure]

theorem lowerImpl_slotTypeChecks {module : Core.Module} {index : ImplId} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ()) (lookup : module.impls[index]? = some impl) :
    (GIR.checkAll (lowerImpl module impl).slots.toList.zipIdx fun (sl, position) => do
      unless sl.var == position do
        throw s!"slot {position} must describe variable {position}, found variable {sl.var}"
      let parameterRefSliceSlot :=
        sl.var < (lowerImpl module impl).params.length &&
          (lowerImpl module impl).params[sl.var]? == some sl.ty && sl.ty.isRefSlice
      unless sl.ty.storable || parameterRefSliceSlot do
        throw s!"the slot of variable {sl.var} has a type no variable may have") =
      (Except.ok () : Except String Unit) := by
  have checked := validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
  have variables := (checkImpl_metadata_checks checked).2
  apply Origins.checkAll_ok_of_forall
  intro pair member
  obtain ⟨sl, position⟩ := pair
  have slotLookup := List.mk_mem_zipIdx_iff_getElem?.mp member
  change (impl.vars.mapIdx (fun position localVar =>
    (⟨localVar.ty, localVar.kind, localVar.scope, position⟩ : Slot))).toList[position]? = some sl at slotLookup
  rw [Array.getElem?_toList, Array.getElem?_mapIdx] at slotLookup
  cases localLookup : impl.vars[position]? with
  | none => simp [localLookup] at slotLookup
  | some localVar =>
    simp only [localLookup, Option.map_some, Option.some.injEq] at slotLookup
    subst sl
    have one := (forAll_ok _ _).mp variables (localVar, position)
      (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using localLookup))
    by_cases stored : localVar.ty.storable = true
    · simp [stored, pure, Except.pure]
    · cases paramLookup : impl.params[position]? with
      | none => simp [stored, paramLookup, chk] at one
      | some param =>
        have bound : position < impl.params.size := (Array.getElem?_eq_some_iff.mp paramLookup).1
        obtain ⟨aligned, parameterVar, parameterLookup, _⟩ :=
          (Core.Sound.validate_modOk module accepted).impl index impl lookup |>.params
            position param paramLookup
        rw [localLookup] at parameterLookup
        cases parameterLookup
        have parameterType : (lowerImpl module impl).params[position]? = some localVar.ty := by
          simp [lowerImpl, List.getElem?_map, paramLookup, tyOfVar, aligned, localLookup]
        have referenceSlice : localVar.ty.isRefSlice = true := by
          by_cases referenceSlice : localVar.ty.isRefSlice = true
          · exact referenceSlice
          · simp [stored, referenceSlice, paramLookup, chk] at one
        have paramsBound : position < (lowerImpl module impl).params.length := by
          simpa only [lowerImpl, List.length_map, Array.length_toList] using bound
        have parameterValue : (lowerImpl module impl).params[position] = localVar.ty := by
          simpa only [List.getElem?_eq_getElem paramsBound, Option.some.injEq] using parameterType
        simp [stored, referenceSlice, parameterValue, paramsBound, pure, Except.pure]

theorem lowerImpl_parameter_types {module : Core.Module} {index : ImplId} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ()) (lookup : module.impls[index]? = some impl) :
    ∀ ty ∈ (lowerImpl module impl).params, ty.paramOk = true := by
  intro ty member
  change ty ∈ impl.params.toList.map (fun param => tyOfVar impl param.var) at member
  obtain ⟨param, paramMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨position, parameterLookup⟩ :=
    Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp paramMember)
  obtain ⟨aligned, localVar, variableLookup, _, shape⟩ :=
    (validate_modOk module accepted).impl index impl lookup |>.params position param parameterLookup
  simpa [tyOfVar, aligned, variableLookup] using shape

theorem lowerImpl_parameterTypeChecks {module : Core.Module} {index : ImplId} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ()) (lookup : module.impls[index]? = some impl) :
    (GIR.checkAll (lowerImpl module impl).params fun ty => do
      unless ty.paramOk do throw "a parameter has a type no parameter may have") =
      (Except.ok () : Except String Unit) := by
  apply Origins.checkAll_ok_of_forall
  intro ty member
  simp [lowerImpl_parameter_types accepted lookup ty member, pure, Except.pure]

theorem lowerContextAt_parameterTypeChecks {module : Core.Module} {index : ImplId}
    {impl : Core.Impl} (ctx : Core.Context)
    (accepted : Core.validate module = .ok ()) (lookup : module.impls[index]? = some impl) :
    (GIR.checkAll (lowerContextAt module ctx impl).params fun ty => do
      unless ty.paramOk do throw "a parameter has a type no parameter may have") =
      (Except.ok () : Except String Unit) :=
  lowerImpl_parameterTypeChecks accepted lookup

end Goose.Lower.Validation
