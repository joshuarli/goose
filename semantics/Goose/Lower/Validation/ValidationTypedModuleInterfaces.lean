import Goose.Lower.Validation.ValidationTypedModuleFunctions
import Goose.Lower.Validation.ValidationTypedModuleEntry
import Goose.Lower.Validation.ValidationTypedModuleGlobalInterface

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lower_info_entry_types {module : Core.Module} (accepted : Core.validate module = .ok ())
    {info : FnInfo} (member : info ∈ (lower module).infos) :
    ∃ block, info.f.blocks[0]? = some block ∧ block.params.map (·.2) = info.f.params.map VTy.data := by
  obtain ⟨_, source⟩ := lower_info_source accepted member
  rcases source with ⟨contextIndex, context, impl, contextAt, implAt, same⟩ |
    ⟨globalIndex, global, globalAt, same⟩
  · rw [same]
    exact lowerContext_entry_types module context impl
  · rw [same]
    exact lowerGlobal_entry_types module global

theorem lower_info_resultTypeChecks {module : Core.Module} (accepted : Core.validate module = .ok ())
    {info : FnInfo} (member : info ∈ (lower module).infos) :
    (GIR.checkAll info.f.results fun ty => do
      unless !ty.isRefSlice do throw "a reference-to-slice type is only valid for a parameter") =
      (Except.ok () : Except String Unit) := by
  obtain ⟨_, source⟩ := lower_info_source accepted member
  rcases source with ⟨contextIndex, context, impl, contextAt, implAt, same⟩ |
    ⟨globalIndex, global, globalAt, same⟩
  · rw [same]
    exact lowerImpl_resultTypeChecks accepted implAt
  · rw [same]
    exact lowerGlobal_resultTypeChecks accepted globalAt

theorem lower_info_slotTypeChecks {module : Core.Module} (accepted : Core.validate module = .ok ())
    {info : FnInfo} (member : info ∈ (lower module).infos) :
    (GIR.checkAll info.f.slots.toList.zipIdx fun (slot, position) => do
      unless slot.var == position do
        throw s!"slot {position} must describe variable {position}, found variable {slot.var}"
      let parameterRefSliceSlot := slot.var < info.f.params.length &&
        info.f.params[slot.var]? == some slot.ty && slot.ty.isRefSlice
      unless slot.ty.storable || parameterRefSliceSlot do
        throw s!"the slot of variable {slot.var} has a type no variable may have") =
      (Except.ok () : Except String Unit) := by
  obtain ⟨_, source⟩ := lower_info_source accepted member
  rcases source with ⟨contextIndex, context, impl, contextAt, implAt, same⟩ |
    ⟨globalIndex, global, globalAt, same⟩
  · rw [same]
    exact lowerImpl_slotTypeChecks accepted implAt
  · rw [same]
    exact lowerGlobal_slotTypeChecks module global

theorem lower_info_interface_resolved {module : Core.Module} (accepted : Core.validate module = .ok ())
    {info : FnInfo} (member : info ∈ (lower module).infos) :
    ∀ type ∈ info.f.params ++ info.f.results ++ info.f.slots.toList.map (·.ty),
      Core.checkResolvedType module type = .ok () := by
  obtain ⟨_, source⟩ := lower_info_source accepted member
  rcases source with ⟨contextIndex, context, impl, contextAt, implAt, same⟩ |
    ⟨globalIndex, global, globalAt, same⟩
  · rw [same]
    exact lowerImpl_interface_resolved accepted implAt
  · rw [same]
    exact lowerGlobal_interface_resolved accepted (Array.mem_toList_iff.mpr (Array.mem_of_getElem? globalAt))

end Goose.Lower.Validation
