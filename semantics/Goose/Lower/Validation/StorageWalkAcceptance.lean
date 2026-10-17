import Goose.Lower.Validation.StorageWalkSourceFunctions
import Goose.Lower.Validation.InterfaceTypes
import Goose.Lower.Validation.Entry

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lower_func_storageWalkGraph {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ContextId} {func : Func} (lookup : (lower module).funcs[index]? = some func) :
    Nonempty (StorageWalkGraph func) := by
  cases contextAt : module.contexts[index]? with
  | none => simp [lower, Array.getElem?_map, contextAt] at lookup
  | some context =>
    obtain ⟨impl, implAt, contextChecked⟩ := (validate_modOk module accepted).ctx index context contextAt
    have lowered := lower_func_at contextAt implAt
    have same : lowerContextAt module context impl = func := Option.some.inj (lowered.symm.trans lookup)
    rw [← same]
    exact lowerContextAt_storageWalkGraph
      (validate_implementation_checks accepted (Array.mem_toList_iff.mpr (Array.mem_of_getElem? implAt))) context

theorem lower_global_storageWalkGraph {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : GlobalId} {global : GIR.Global} (lookup : (lower module).globals[index]? = some global) :
    Nonempty (StorageWalkGraph global.init) := by
  cases globalAt : module.globals[index]? with
  | none => simp [lower, Array.getElem?_map, globalAt] at lookup
  | some source =>
    have same : lowerGlobal module source = global := by
      simpa only [lower, Array.getElem?_map, globalAt, Option.map_some, Option.some.injEq] using lookup
    rw [← same]
    exact lowerGlobal_storageWalkGraph (validate_global_checks accepted globalAt)

theorem lower_labelled_storageWalkGraph {module : Core.Module} (accepted : Core.validate module = .ok ())
    {label : String} {func : Func} (member : (label, func) ∈ (lower module).labelled) :
    Nonempty (StorageWalkGraph func) := by
  simp only [GIR.Module.labelled, List.mem_append, List.mem_map] at member
  rcases member with ⟨function, member, same⟩ | ⟨global, member, same⟩
  · obtain ⟨_, rfl⟩ := Prod.mk.inj same
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    exact lower_func_storageWalkGraph accepted lookup
  · obtain ⟨_, rfl⟩ := Prod.mk.inj same
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    exact lower_global_storageWalkGraph accepted lookup

theorem lower_walkScopes_storage {module : Core.Module} (accepted : Core.validate module = .ok ())
    (info : FnInfo) (member : info ∈ (lower module).infos) :
    (walkScopes info.label info.f).storage = none := by
  simp only [GIR.Module.infos, List.mem_map] at member
  obtain ⟨⟨label, func⟩, member, same⟩ := member
  cases same
  obtain ⟨graph⟩ := lower_labelled_storageWalkGraph accepted member
  exact graph.walkScopes_storage label

theorem lower_checkStorageWalk {module : Core.Module} (accepted : Core.validate module = .ok ()) :
    (checkAll ((lower module).infos.map fun info => walkScopes info.label info.f) fun walk => do
      if let some message := walk.storage then violation .v030 message) = .ok () := by
  have clean : ∀ walk ∈ ((lower module).infos.map fun info => walkScopes info.label info.f), walk.storage = none := by
    intro walk member
    obtain ⟨info, infoMember, rfl⟩ := List.mem_map.mp member
    exact lower_walkScopes_storage accepted info infoMember
  generalize ((lower module).infos.map fun info => walkScopes info.label info.f) = walks at clean ⊢
  induction walks with
  | nil => rfl
  | cons walk rest ih =>
    have none := clean walk (by simp)
    simp only [checkAll, none, bind, Except.bind, pure, Except.pure]
    apply ih
    intro next member
    exact clean next (by simp [member])

#print axioms lower_func_storageWalkGraph
#print axioms lower_global_storageWalkGraph
#print axioms lower_walkScopes_storage
#print axioms lower_checkStorageWalk

end Goose.Lower.Validation
