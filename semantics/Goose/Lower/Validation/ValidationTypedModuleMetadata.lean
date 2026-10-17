import Goose.Lower.Validation.ValidationTypedModuleEntry
import Goose.Lower.Validation.ScopeAcceptance
import Goose.Lower.Validation.Entry
import Goose.Lower.Validation.InterfaceTypes
import Goose.Lower.Validation.ResolvedTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerGlobal_resultTypeChecks {module : Core.Module} {index : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ()) (lookup : module.globals[index]? = some global) :
    (GIR.checkAll (lowerGlobal module global).init.results fun ty => do
      unless !ty.isRefSlice do throw "a reference-to-slice type is only valid for a parameter") =
      (Except.ok () : Except String Unit) := by
  have checked := checkGlobal_ok module index global (validate_global_checks accepted lookup)
  have notReference : global.ty.isRefSlice = false := by
    cases type : global.ty <;> simp_all [Ty.isRefLike, Ty.isRefSlice]
  simp [lowerGlobal, checkAll, notReference, pure, Except.pure, bind, Except.bind]

theorem lowerGlobal_slotTypeChecks (module : Core.Module) (global : Core.Global) :
    (GIR.checkAll (lowerGlobal module global).init.slots.toList.zipIdx fun (sl, position) => do
      unless sl.var == position do
        throw s!"slot {position} must describe variable {position}, found variable {sl.var}"
      let parameterRefSliceSlot :=
        sl.var < (lowerGlobal module global).init.params.length &&
          (lowerGlobal module global).init.params[sl.var]? == some sl.ty && sl.ty.isRefSlice
      unless sl.ty.storable || parameterRefSliceSlot do
        throw s!"the slot of variable {sl.var} has a type no variable may have") =
      (Except.ok () : Except String Unit) := rfl

theorem lower_entry_scopes_origins_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    checkEntryAndGlobals (lower module) = .ok () ∧
    (checkAll ((lower module).infos.map fun info => walkScopes info.label info.f) fun walk => do
      if let some message := walk.scopes then violation .v040 message) = .ok () ∧
    (checkAll (lower module).infos fun info => checkOrigins (lower module).profile info.label info.f) = .ok () :=
  ⟨lower_checkEntryAndGlobals accepted, lower_checkScopes accepted, lower_checkOrigins accepted⟩

end Goose.Lower.Validation
