import Goose.Lower.Validation.Acceptance

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem checkImpl_variable_bounds {module : Core.Module} {impl : Core.Impl}
    (checked : Core.checkImpl module impl = .ok ()) :
    ∀ localVar ∈ impl.vars.toList, localVar.org < module.origins.size ∧
      localVar.scope < (blockScopes none impl.body).length := by
  unfold Core.checkImpl at checked
  cases order : scopeOrderError (blockScopes none impl.body) 0 with
  | some message =>
    simp only [order] at checked
    inv at checked
  | none =>
    simp only [order] at checked
    inv at checked
    obtain ⟨_, _, _, _, origins, _, scopes, _, _, _, _⟩ := checked
    intro localVar member
    have origin := (forAll_ok _ _).mp origins localVar member
    have scope := (forAll_ok _ _).mp scopes localVar member
    constructor
    · by_cases bound : localVar.org < module.origins.size
      · exact bound
      · simp [bound, Core.reject] at origin
    · by_cases bound : localVar.scope < (blockScopes none impl.body).length
      · exact bound
      · simp [bound, Core.reject] at scope

theorem lowerImpl_slot_scopes {module : Core.Module} {index : ImplId} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ()) (lookup : module.impls[index]? = some impl) :
    ∀ slot ∈ (lowerImpl module impl).slots.toList,
      slot.scope < (lowerImpl module impl).scopes.size := by
  intro slot member
  have checked := validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
  change slot ∈ (impl.vars.mapIdx (fun position localVar =>
    (⟨localVar.ty, localVar.kind, localVar.scope, position⟩ : Slot))).toList at member
  obtain ⟨position, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  rw [Array.getElem?_mapIdx] at row
  cases localRow : impl.vars[position]? with
  | none => simp [localRow] at row
  | some localVar =>
    simp only [localRow, Option.map_some, Option.some.injEq] at row
    subst slot
    have bound := (checkImpl_variable_bounds checked localVar
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? localRow))).2
    simpa [lowerImpl, lowerImplFromState, scopeParents] using bound

theorem lowerImpl_function_origin {module : Core.Module} {index : ImplId} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ()) (lookup : module.impls[index]? = some impl)
    {origin : OriginId} (present : (lowerImpl module impl).org = some origin) :
    origin < (lower module).origins.size := by
  have checked := validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
  change impl.vars[0]?.map (·.org) = some origin at present
  cases row : impl.vars[0]? with
  | none => simp [row] at present
  | some localVar =>
    simp only [row, Option.map_some, Option.some.injEq] at present
    subst origin
    exact (checkImpl_variable_bounds checked localVar
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row))).1

theorem lowerGlobal_function_origin {module : Core.Module} {index : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ()) (lookup : module.globals[index]? = some global)
    {origin : OriginId} (present : (lowerGlobal module global).init.org = some origin) :
    origin < (lower module).origins.size := by
  have equal : global.org = origin := Option.some.inj present
  subst origin
  exact checkGlobal_origin_bound (validate_global_checks accepted lookup)

end Goose.Lower.Validation
