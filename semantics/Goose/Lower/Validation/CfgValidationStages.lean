import Goose.Lower.Validation.CfgReconstructedModule
import Goose.Lower.Validation.CfgAcceptedNoReturn

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lower_cfgStages_of_accepted_source_certificates {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (certificates : LowerCfgSourceCertificates module) :
    checkAll (lower module).infos (fun info => checkCfg info.label info.f info.vt) = .ok () ∧
      checkUnreachable (lower module) = .ok () :=
  ⟨lower_checkCfg_of_accepted_source_certificates accepted certificates,
    lower_checkUnreachable_of_accepted accepted⟩

end Goose.Lower.Validation
