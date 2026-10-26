import Goose.Proofs.ConstructionRootedBackingPrefixes

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct

private theorem flat_not_variable (ty : Ty) (flat : ty.flat = true) : ty.variableElement = false := by
  cases ty with
  | arr element count => exact flat_not_variable element flat
  | _ => simp_all [Ty.flat, Ty.variableElement]
termination_by sizeOf ty

private theorem flat_not_nonfixed (ty : Ty) (flat : ty.flat = true) : ty.nonfixed = false := by
  cases ty with
  | arr element count => exact flat_not_variable element flat
  | _ => simp_all [Ty.flat, Ty.nonfixed]

private theorem flat_fields (types : TyList) (flat : types.flat = true) :
    ∀ ty ∈ types.toList, ty.flat = true := by
  cases types with
  | nil => intro ty member; cases member
  | cons first rest =>
    have parts : first.flat = true ∧ rest.flat = true := by simpa only [TyList.flat, Bool.and_eq_true] using flat
    intro ty member
    rcases List.mem_cons.mp member with same | member
    · subst ty; exact parts.1
    · exact flat_fields rest parts.2 ty member
termination_by sizeOf types

theorem ValueRepresentation.flat_storageBacked (layout : LayoutEnv) (state : ExecutionState)
    (ty : Ty) (value : Value) (represented : ValueRepresentation ty value) (flat : ty.flat = true) :
    ValueStorageBacked layout state value := by
  revert flat
  induction represented with
  | integer ty value => intro _; exact .integer ty value
  | boolean value => intro _; exact .boolean value
  | unit => intro _; exact .unit
  | reference mutability ty location => intro _; exact .reference location
  | slice mutability ty location start count => intro _; exact .slice location start count
  | array element count values inline length children ih =>
    intro flat
    exact .array values (fun value member => ih value member flat)
  | record id types values length children ih =>
    intro flat
    apply ValueStorageBacked.record id values
    intro value member
    obtain ⟨index, found⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    have inside : index < types.toList.length := by
      have bound := (Array.getElem?_eq_some_iff.mp found).1
      omega
    let field := types.toList[index]
    have selected : types.toList[index]? = some field := List.getElem?_eq_getElem inside
    exact ih index field value selected found (flat_fields types flat field (List.mem_of_getElem? selected))
  | stored ty stored nonfixed logicalType =>
    intro flat
    have fixed := flat_not_nonfixed ty flat
    rw [nonfixed] at fixed
    cases fixed

private theorem initial_backing_noStored (layout : LayoutEnv) (value : Value)
    (backed : ValueStorageBacked layout .initial value) (stored : StoredValue) :
    ¬ StoredOccurrence value stored := by
  intro occurrence
  have impossible := backed.occurrence_backing layout .initial value stored occurrence
  cases impossible with
  | detached storage element present detached type interval => cases present
  | named id storage destination count present named binding backing type start progress element elementType interval => cases present

theorem ValueRepresentation.flat_noStoredOccurrence (ty : Ty) (value : Value)
    (represented : ValueRepresentation ty value) (flat : ty.flat = true) (stored : StoredValue) :
    ¬ StoredOccurrence value stored :=
  initial_backing_noStored (⟨#[]⟩ : LayoutEnv) value
    (represented.flat_storageBacked (⟨#[]⟩ : LayoutEnv) .initial ty value flat) stored

theorem ValueRepresentation.checked_fixed_storageBacked (module : Module) (layout : LayoutEnv)
    (state : ExecutionState) (ty : Ty) (value : Value) (represented : ValueRepresentation ty value)
    (checked : checkType module ty = .ok ()) (fixed : ty.nonfixed = false) :
    ValueStorageBacked layout state value := by
  cases represented with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference mutability ty location => exact .reference location
  | slice mutability ty location start count => exact .slice location start count
  | array element count values inline length children =>
    have flat : element.flat = true := by
      cases flat : element.flat with
      | true => rfl
      | false =>
        have fixedElement : element.variableElement = false := fixed
        simp [checkType, flat, fixedElement, Core.reject, bind, Except.bind] at checked
    exact (ValueRepresentation.array element count values inline length children).flat_storageBacked
      layout state (.arr element count) (.fixed values) flat
  | record id types values length children =>
    have flat : types.flat = true := by
      cases flat : types.flat with
      | true => rfl
      | false => simp [checkType, flat, Core.reject, bind, Except.bind] at checked
    exact (ValueRepresentation.record id types values length children).flat_storageBacked
      layout state (.structT id types) (.record id values) flat
  | stored ty stored nonfixed logicalType => rw [nonfixed] at fixed; cases fixed

theorem ValueRepresentation.checked_fixed_noStoredOccurrence (module : Module) (ty : Ty) (value : Value)
    (represented : ValueRepresentation ty value) (checked : checkType module ty = .ok ())
    (fixed : ty.nonfixed = false) (stored : StoredValue) : ¬ StoredOccurrence value stored :=
  initial_backing_noStored (⟨#[]⟩ : LayoutEnv) value
    (represented.checked_fixed_storageBacked module (⟨#[]⟩ : LayoutEnv) .initial ty value checked fixed) stored

#print axioms ValueRepresentation.checked_fixed_storageBacked
#print axioms ValueRepresentation.checked_fixed_noStoredOccurrence

#print axioms ValueRepresentation.flat_storageBacked
#print axioms ValueRepresentation.flat_noStoredOccurrence
end Goose.Proofs.ConstructionRepresentation
