import Goose.Lower.Validation.Acceptance
import Goose.Lower.Validation.ValidationTypedModule
import Goose.Lower.Validation.SourceSymbolSourceCheck
import Goose.Lower.Validation.CfgAcceptedModule
import Goose.Lower.Validation.StorageWalkAcceptance
import Goose.Lower.Validation.ValidationStructuralStorage
import Goose.Lower.Validation.PermissionPreservationAccepted
import Goose.Lower.Validation.AdmittedSourceModule
import Goose.Lower.Validation.SourceSummaryAccepted

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lower_storagePermission_stage_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    (checkAll ((lower module).infos.zip ((lower module).infos.map fun info => walkScopes info.label info.f))
      fun (info, walk) => do
        if let some message := walk.storage then violation .v030 message
        checkStorage (lower module) info.label info.f info.vt
        checkPermissions (lower module) info.label info.f info.vt) = .ok () := by
  have grouped : ∀ infos : List FnInfo,
      (∀ info ∈ infos, (walkScopes info.label info.f).storage = none ∧
        checkStorage (lower module) info.label info.f info.vt = .ok () ∧
        checkPermissions (lower module) info.label info.f info.vt = .ok ()) →
      (checkAll (infos.zip (infos.map fun info => walkScopes info.label info.f)) fun (info, walk) => do
        if let some message := walk.storage then violation .v030 message
        checkStorage (lower module) info.label info.f info.vt
        checkPermissions (lower module) info.label info.f info.vt) = .ok () := by
    intro infos
    induction infos with
    | nil => intro _; rfl
    | cons info rest ih =>
      intro checked
      have head := checked info (by simp)
      simp only [List.map_cons, List.zip_cons_cons, checkAll, head.1, head.2.1, head.2.2,
        bind, Except.bind]
      exact ih (fun next member => checked next (by simp [member]))
  exact grouped _ (fun info member => ⟨lower_walkScopes_storage accepted info member,
    GIR.checkAll_ok (lower_checkStorage_of_accepted accepted) info member,
    GIR.checkAll_ok (lower_permission_stage_of_accepted accepted) info member⟩)

theorem lower_validate_of_replacement_checks {module : Core.Module}
    (accepted : Core.validate module = .ok ())
    (replacement : (checkAll (lower module).infos fun info =>
      checkShrinkReplace (lower module) info.label info.f info.vt) = .ok ()) :
    GIR.validate (lower module) = .ok () := by
  obtain ⟨entry, structs, types, scopes, origins⟩ := lower_typedValidation_of_accepted accepted
  obtain ⟨cfg, unreachable⟩ := lower_cfgStages_of_accepted accepted
  have admitted : asCheck .v050 "declared regions"
      ((lower module).checkAdmittedRegions (lower module).implTypes
        (resultRoots (lower module) (lower module).implTypes) (lower module).rootCount) = .ok () := by
    simp only [accepted_module_checkAdmittedRegions accepted, asCheck]
  exact (gir_validate_stages (lower module)).mpr
    ⟨entry, SourceSymbolSource.lower_checkSymbols accepted, structs, types, cfg, unreachable,
      lower_storagePermission_stage_of_accepted accepted, scopes, admitted,
      accepted_module_checkSummaries accepted, replacement, lower_checkEvidence module, origins⟩

theorem lower_validate_pilot_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (profile : module.profile = .pilot) :
    GIR.validate (lower module) = .ok () := by
  apply lower_validate_of_replacement_checks accepted
  apply Origins.checkAll_ok_of_forall
  intro info member
  rw [checkShrinkReplace_eq]
  have loweredProfile : (lower module).profile = .pilot := profile
  have separate : (ArtifactProfile.pilot == ArtifactProfile.shrink) = false := rfl
  simp only [loweredProfile, separate, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]

#print axioms lower_storagePermission_stage_of_accepted
#print axioms lower_validate_of_replacement_checks
#print axioms lower_validate_pilot_of_accepted

end Goose.Lower.Validation
