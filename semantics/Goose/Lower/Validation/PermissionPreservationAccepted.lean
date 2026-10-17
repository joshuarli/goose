import Goose.Lower.Validation.PermissionSourceInduction
import Goose.Lower.Validation.PermissionPreservationEntry
import Goose.Lower.Validation.ValidationTypedModuleFunctions

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerImpl_source_permission_state
    {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (row : module.impls[index]? = some impl) :
    PermissionState (lower module) (lowerImpl module impl)
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl) := by
  have checked := checkImpl_ok module impl (validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row)))
  obtain ⟨bodyType, finish, source, _⟩ := checked.body
  apply implementation_permission_state_of_body checked rfl rfl
  intro pre before after value generated transfer run
  exact permission_source_block impl.body (implEnv module impl) (lowerImpl module impl) impl.results.toList
    (PermissionSourceTables.lowerImpl impl rfl rfl) source generated (show LoopBuilderFrames none before from trivial) (Nat.zero_le _) transfer run

theorem lowerContextAt_source_permission_state
    {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (row : module.impls[index]? = some impl) (context : Context) :
    PermissionState (lower module) (lowerContextAt module context impl)
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl) := by
  have checked := checkImpl_ok module impl (validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row)))
  obtain ⟨bodyType, finish, source, _⟩ := checked.body
  apply implementation_permission_state_of_body checked rfl rfl
  intro pre before after value generated transfer run
  exact permission_source_block impl.body (implEnv module impl) (lowerContextAt module context impl) impl.results.toList
    (PermissionSourceTables.lowerContextAt context impl rfl rfl) source generated (show LoopBuilderFrames none before from trivial) (Nat.zero_le _) transfer run

theorem lowerGlobal_source_permission_state
    {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : GlobalId} {global : Core.Global} (row : module.globals[index]? = some global) :
    PermissionState (lower module) (lowerGlobal module global).init
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global) := by
  obtain ⟨_, finish, source⟩ := checkGlobal_ok module index global (validate_global_checks accepted row)
  apply global_permission_state_of_expression source rfl
  intro before after value generated run
  exact permission_source_expression global.init (initEnv module index) (lowerGlobal module global).init [global.ty]
    (PermissionSourceTables.lowerGlobal global rfl rfl) source generated run

theorem lowerImpl_source_checkPermissions
    {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (row : module.impls[index]? = some impl) (label : String) :
    checkPermissions (lower module) label (lowerImpl module impl)
      ((lowerImpl module impl).valueTypes (lower module)) = .ok () :=
  implementation_permission_check_of_state accepted row (lowerImpl_source_permission_state accepted row) label

theorem lowerContextAt_source_checkPermissions
    {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (row : module.impls[index]? = some impl) (context : Context) (label : String) :
    checkPermissions (lower module) label (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module)) = .ok () :=
  context_permission_check_of_state accepted row context (lowerContextAt_source_permission_state accepted row context) label

theorem lowerGlobal_source_checkPermissions
    {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : GlobalId} {global : Core.Global} (row : module.globals[index]? = some global) (label : String) :
    checkPermissions (lower module) label (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module)) = .ok () :=
  global_permission_check_of_state accepted row (lowerGlobal_source_permission_state accepted row) label

theorem lower_permission_stage_of_accepted
    {module : Core.Module} (accepted : Core.validate module = .ok ()) :
    (checkAll (lower module).infos fun info =>
      checkPermissions (lower module) info.label info.f info.vt) = .ok () := by
  apply Origins.checkAll_ok_of_forall
  intro info member
  obtain ⟨tables, source⟩ := lower_info_source accepted member
  rw [tables]
  rcases source with ⟨contextIndex, context, impl, contextAt, implAt, same⟩ |
    ⟨globalIndex, global, globalAt, same⟩
  · rw [same]
    exact lowerContextAt_source_checkPermissions accepted implAt context info.label
  · rw [same]
    exact lowerGlobal_source_checkPermissions accepted globalAt info.label

#print axioms lowerImpl_source_permission_state
#print axioms lowerContextAt_source_permission_state
#print axioms lowerGlobal_source_permission_state
#print axioms lowerImpl_source_checkPermissions
#print axioms lowerContextAt_source_checkPermissions
#print axioms lowerGlobal_source_checkPermissions
#print axioms lower_permission_stage_of_accepted

end Goose.Lower.Validation
