import Goose.Lower.Validation.EmittedTypingFunctions
import Goose.Lower.Validation.SnapshotContentsModule
import Goose.Lower.Validation.StorageSourceEntry
import Goose.Lower.ContextLowering

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerImpl_checkStorage_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (row : module.impls[index]? = some impl) (label : String) :
    checkStorage (lower module) label (lowerImpl module impl) ((lowerImpl module impl).valueTypes (lower module)) = .ok () :=
  lowerImpl_source_checkStorage accepted row
    (lowerImpl_emittedBuilder_of_accepted accepted row)
    (lowerImpl_mutableSnapshotGraphs_of_accepted accepted row) label

theorem lowerContextAt_checkStorage_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (row : module.impls[index]? = some impl) (context : Context) (label : String) :
    checkStorage (lower module) label (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module)) = .ok () :=
  lowerContextAt_source_checkStorage accepted row context
    (lowerImpl_emittedBuilder_of_accepted accepted row)
    (lowerContext_mutableSnapshotGraphs_of_accepted accepted row) label

theorem lowerGlobal_checkStorage_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : GlobalId} {global : Core.Global} (row : module.globals[index]? = some global) (label : String) :
    checkStorage (lower module) label (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module)) = .ok () :=
  lowerGlobal_source_checkStorage accepted row
    (lowerGlobal_emittedBuilder_of_accepted accepted row)
    (lowerGlobal_mutableSnapshotGraphs_of_accepted accepted row) label

private theorem lower_function_checkStorage {module : Core.Module} (accepted : Core.validate module = .ok ())
    (func : Func) (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init))
    (label : String) : checkStorage (lower module) label func (func.valueTypes (lower module)) = .ok () := by
  have moduleOk := validate_modOk module accepted
  rcases List.mem_append.mp member with implementation | initializer
  · obtain ⟨index, functionAt⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp implementation)
    cases contextAt : module.contexts[index]? with
    | none => simp [lower, Array.getElem?_map, contextAt] at functionAt
    | some context =>
      obtain ⟨impl, implAt, _⟩ := moduleOk.ctx index context contextAt
      have same : lowerContextAt module context impl = func :=
        Option.some.inj ((lower_func_at contextAt implAt).symm.trans functionAt)
      rw [← same]
      exact lowerContextAt_checkStorage_of_accepted accepted implAt context label
  · obtain ⟨global, globalMember, rfl⟩ := List.mem_map.mp initializer
    change global ∈ (module.globals.map (lowerGlobal module)).toList at globalMember
    simp only [Array.toList_map, List.mem_map] at globalMember
    obtain ⟨source, sourceMember, rfl⟩ := globalMember
    obtain ⟨index, sourceRow⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp sourceMember)
    exact lowerGlobal_checkStorage_of_accepted accepted sourceRow label

private theorem checkAll_success {items : List α} {action : α → Except ε Unit}
    (checked : ∀ item ∈ items, action item = .ok ()) : checkAll items action = .ok () := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [checkAll, checked item (by simp), bind, Except.bind]
    exact ih fun next member => checked next (by simp [member])

theorem lower_checkStorage_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ()) :
    checkAll (lower module).infos (fun info => checkStorage (lower module) info.label info.f info.vt) = .ok () := by
  apply checkAll_success
  intro info member
  unfold GIR.Module.infos at member
  obtain ⟨⟨label, func⟩, labelledMember, rfl⟩ := List.mem_map.mp member
  apply lower_function_checkStorage accepted func ?_ label
  unfold GIR.Module.labelled at labelledMember
  rcases List.mem_append.mp labelledMember with implementation | initializer
  · obtain ⟨body, present, same⟩ := List.mem_map.mp implementation
    have sameBody : body = func := congrArg Prod.snd same
    exact List.mem_append_left _ (sameBody ▸ present)
  · obtain ⟨global, present, same⟩ := List.mem_map.mp initializer
    have initMember : global.init ∈ (lower module).globals.toList.map (·.init) :=
      List.mem_map.mpr ⟨global, present, rfl⟩
    have sameInit : global.init = func := congrArg Prod.snd same
    exact List.mem_append_right _ (sameInit ▸ initMember)

end Goose.Lower.Validation
