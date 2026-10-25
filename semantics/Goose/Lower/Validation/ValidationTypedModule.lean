import Goose.Lower.Validation.ValidationTypedModuleChecking
import Goose.Lower.Validation.ValidationTypedModuleStructure
import Goose.Lower.Validation.ValidationTypedModuleMetadata

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lower_typedValidation_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    checkEntryAndGlobals (lower module) = .ok () ∧
    checkStructTypes (lower module) = .ok () ∧
    (checkAll (lower module).infos fun info => checkTypes (lower module) info.label info.f info.vt) = .ok () ∧
    (checkAll ((lower module).infos.map fun info => walkScopes info.label info.f) fun walk => do
      if let some message := walk.scopes then violation .v040 message) = .ok () ∧
    (checkAll (lower module).infos fun info => checkOrigins (lower module).profile info.label info.f) = .ok () := by
  obtain ⟨entry, scopes, origins⟩ := lower_entry_scopes_origins_of_accepted accepted
  exact ⟨entry, lower_checkStructTypes_of_accepted accepted, lower_checkTypes_of_accepted accepted, scopes, origins⟩

end Goose.Lower.Validation
