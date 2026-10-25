import Goose.Lower.Validation.ValidationTypedModuleEntry
import Goose.Lower.Validation.ScopeAcceptance
import Goose.Lower.Validation.Entry
import Goose.Lower.Validation.ValidationTypedModuleGlobalInterface

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lower_entry_scopes_origins_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    checkEntryAndGlobals (lower module) = .ok () ∧
    (checkAll ((lower module).infos.map fun info => walkScopes info.label info.f) fun walk => do
      if let some message := walk.scopes then violation .v040 message) = .ok () ∧
    (checkAll (lower module).infos fun info => checkOrigins (lower module).profile info.label info.f) = .ok () :=
  ⟨lower_checkEntryAndGlobals accepted, lower_checkScopes accepted, lower_checkOrigins accepted⟩

end Goose.Lower.Validation
