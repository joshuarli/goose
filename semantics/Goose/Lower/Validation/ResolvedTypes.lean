import Goose.Lower.Validation.Entry

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem resolvedType_eq_of_tables {source target : Core.Module}
    (profile : source.profile = target.profile) (structs : source.structs = target.structs)
    (ty : Ty) : Core.checkResolvedType source ty = Core.checkResolvedType target ty := by
  cases ty with
  | structT id fields =>
    simp only [Core.checkResolvedType, Module.structType?, profile, structs,
      resolvedTypes_eq_of_tables profile structs fields]
    rfl
  | arr elem size | grow elem | ref mu elem | slice mu elem =>
    exact resolvedType_eq_of_tables profile structs elem
  | growshrink elem =>
    simp only [Core.checkResolvedType, profile, resolvedType_eq_of_tables profile structs elem]
  | limited elem capacity =>
    simp only [Core.checkResolvedType, profile, resolvedType_eq_of_tables profile structs elem]
  | tuple types => exact resolvedTypes_eq_of_tables profile structs types
  | int _ | bool | unit => rfl
termination_by sizeOf ty

theorem resolvedTypes_eq_of_tables {source target : Core.Module}
    (profile : source.profile = target.profile) (structs : source.structs = target.structs)
    (types : TyList) : Core.checkResolvedTypes source types = Core.checkResolvedTypes target types := by
  cases types with
  | nil => rfl
  | cons ty rest =>
    simp only [Core.checkResolvedTypes, resolvedType_eq_of_tables profile structs ty,
      resolvedTypes_eq_of_tables profile structs rest]
termination_by sizeOf types

end

theorem fixedByteSize_eq_of_structs {source target : Core.Module}
    (structs : source.structs = target.structs) (ty : Ty) :
    source.fixedByteSize? ty = target.fixedByteSize? ty := by
  cases ty with
  | arr elem size =>
    simp only [Core.Module.fixedByteSize?, fixedByteSize_eq_of_structs structs elem]
  | structT id fields =>
    simp only [Core.Module.fixedByteSize?, Core.Module.structType?, structs]
    rfl
  | _ => rfl
termination_by sizeOf ty

theorem checkStructTables_empty_metadata {source target : Core.Module}
    (profile : source.profile = target.profile) (structs : source.structs = target.structs)
    (types : target.types = #[]) (globals : target.globals = #[]) (impls : target.impls = #[])
    (checked : Core.checkStructTables source = .ok ()) :
    Core.checkStructTables target = .ok () := by
  unfold Core.checkStructTables at checked
  by_cases forbidden : (source.profile == .pilot && !source.structs.isEmpty) = true
  · simp [forbidden, chk] at checked
  · simp only [forbidden] at checked
    obtain ⟨_, structuresChecked, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
    unfold Core.checkStructTables
    simp only [← profile, ← structs, types, globals, impls, forbidden,
      ← resolvedType_eq_of_tables profile structs, ← fixedByteSize_eq_of_structs structs]
    rw [structuresChecked]
    simp [Core.forAll, pure, Except.pure, bind, Except.bind]

theorem lower_structDescriptorTables {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    let lowered := lower module
    Core.checkStructTables
      { files := lowered.files, types := #[], globals := #[], impls := #[], contexts := #[],
        entry := 0, origins := lowered.origins, profile := lowered.profile,
        structs := lowered.structs } = .ok () :=
  checkStructTables_empty_metadata (source := module) rfl rfl rfl rfl rfl
    (Core.Sound.validate_modOk module accepted).structTables

private theorem forIn_checks_member {items : List α} {check : α → Core.V Unit}
    (checked : forIn items PUnit.unit (fun item _ => do
      check item
      pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit) :
    ∀ item ∈ items, check item = .ok () := by
  induction items with
  | nil => simp
  | cons item rest inductionHypothesis =>
    rw [List.forIn_cons] at checked
    cases first : check item with
    | error error => simp [first, bind, Except.bind] at checked
    | ok value =>
      cases value
      simp only [first, bind, Except.bind, pure, Except.pure] at checked
      intro next member
      rcases List.mem_cons.mp member with rfl | member
      · exact first
      · exact inductionHypothesis checked next member

theorem checkStructTables_global_resolved {module : Core.Module}
    (checked : Core.checkStructTables module = .ok ()) {global : Core.Global}
    (member : global ∈ module.globals.toList) :
    Core.checkResolvedType module global.ty = .ok () := by
  unfold Core.checkStructTables at checked
  by_cases forbidden : (module.profile == .pilot && !module.structs.isEmpty) = true
  · simp [forbidden, chk] at checked
  · simp only [forbidden] at checked
    obtain ⟨_, _, checked⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
    obtain ⟨_, _, checked⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
    obtain ⟨_, globals, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
    rw [← Array.forIn_toList] at globals
    exact forIn_checks_member globals global member

private theorem forIn_yield_member {items : List α} {check : α → Core.V (ForInStep PUnit.{1})}
    (yielded : ∀ item step, check item = .ok step → step = .yield PUnit.unit)
    (checked : forIn items PUnit.unit (fun item _ => check item) = .ok PUnit.unit) :
    ∀ item ∈ items, check item = .ok (.yield PUnit.unit) := by
  induction items with
  | nil => simp
  | cons item rest inductionHypothesis =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, first, remaining⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
    have equal := yielded item step first
    subst step
    intro next member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact inductionHypothesis remaining next member

theorem checkStructTables_impl_resolved {module : Core.Module}
    (checked : Core.checkStructTables module = .ok ()) {impl : Core.Impl}
    (member : impl ∈ module.impls.toList) :
    (∀ localVar ∈ impl.vars.toList, Core.checkResolvedType module localVar.ty = .ok ()) ∧
      (∀ result ∈ impl.results.toList, Core.checkResolvedType module result = .ok ()) := by
  unfold Core.checkStructTables at checked
  by_cases forbidden : (module.profile == .pilot && !module.structs.isEmpty) = true
  · simp [forbidden, chk] at checked
  · simp only [forbidden] at checked
    obtain ⟨_, _, checked⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
    obtain ⟨_, _, checked⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
    obtain ⟨_, _, checked⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
    obtain ⟨_, implementations, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
    rw [← Array.forIn_toList] at implementations
    have yielded : ∀ (item : Core.Impl) (step : ForInStep PUnit.{1}), (do
        for localVar in item.vars do Core.checkResolvedType module localVar.ty
        for result in item.results do Core.checkResolvedType module result
        pure (ForInStep.yield PUnit.unit)) = .ok step → step = .yield PUnit.unit := by
      intro item step one
      obtain ⟨_, _, one⟩ := (Core.Sound.ex_bind_ok _ _ _).mp one
      obtain ⟨_, _, one⟩ := (Core.Sound.ex_bind_ok _ _ _).mp one
      simpa [pure, Except.pure] using one.symm
    have one := forIn_yield_member yielded implementations impl member
    obtain ⟨_, localVars, one⟩ := (Core.Sound.ex_bind_ok _ _ _).mp one
    obtain ⟨_, results, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp one
    rw [← Array.forIn_toList] at localVars results
    exact ⟨forIn_checks_member localVars, forIn_checks_member results⟩

theorem lowerImplAt_interface_resolved {module : Core.Module} {index : ImplId} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ()) (lookup : module.impls[index]? = some impl) :
    ∀ ty ∈ (lowerImplAt module index impl).params ++ (lowerImplAt module index impl).results ++
      (lowerImplAt module index impl).slots.toList.map (·.ty),
      Core.checkResolvedType module ty = .ok () := by
  have implMember : impl ∈ module.impls.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup)
  have metadata := checkStructTables_impl_resolved
    (Core.Sound.validate_modOk module accepted).structTables implMember
  intro ty member
  simp only [List.mem_append] at member
  rcases member with (parameter | result) | slot
  · change ty ∈ impl.params.toList.map (fun param => tyOfVar impl param.var) at parameter
    obtain ⟨param, member, rfl⟩ := List.mem_map.mp parameter
    obtain ⟨position, parameterLookup⟩ :=
      Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    obtain ⟨aligned, localVar, localLookup, _⟩ :=
      (Core.Sound.validate_modOk module accepted).impl index impl lookup |>.params
        position param parameterLookup
    rw [aligned]
    simp only [tyOfVar, localLookup]
    exact metadata.1 localVar (Array.mem_toList_iff.mpr (Array.mem_of_getElem? localLookup))
  · exact metadata.2 ty result
  · obtain ⟨sl, member, equality⟩ := List.mem_map.mp slot
    obtain ⟨position, slotLookup⟩ :=
      Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    change (impl.vars.mapIdx (fun position localVar =>
      (⟨localVar.ty, localVar.kind, localVar.scope, position⟩ : Slot)))[position]? = some sl at slotLookup
    rw [Array.getElem?_mapIdx] at slotLookup
    cases localLookup : impl.vars[position]? with
    | none => simp [localLookup] at slotLookup
    | some localVar =>
      simp only [localLookup, Option.map_some, Option.some.injEq] at slotLookup
      subst sl
      subst ty
      exact metadata.1 localVar (Array.mem_toList_iff.mpr (Array.mem_of_getElem? localLookup))

theorem lowerGlobal_interface_resolved {module : Core.Module} {global : Core.Global}
    (accepted : Core.validate module = .ok ()) (member : global ∈ module.globals.toList) :
    ∀ ty ∈ (lowerGlobal module global).init.params ++ (lowerGlobal module global).init.results ++
      (lowerGlobal module global).init.slots.toList.map (·.ty),
      Core.checkResolvedType module ty = .ok () := by
  intro ty memberType
  have resolved := checkStructTables_global_resolved
    (Core.Sound.validate_modOk module accepted).structTables member
  simp only [lowerGlobal, List.nil_append, List.append_nil, Array.toList_empty,
    List.map_nil, List.mem_singleton] at memberType
  subst ty
  exact resolved

end Goose.Lower.Validation
