import Goose.Lower.Validation.CfgValidationStages
import Goose.Lower.Validation.EmittedTypingFunctions
import Goose.Lower.Validation.SnapshotContentsModule

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lower_sourceCfgCertificates_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) : LowerCfgSourceCertificates module := by
  constructor
  · intro index context impl contextRow implRow
    exact ⟨lowerImpl_emittedBuilder_of_accepted accepted implRow,
      lowerContext_mutableSnapshotGraphs_of_accepted accepted implRow⟩
  · intro index global globalRow
    exact ⟨lowerGlobal_emittedBuilder_of_accepted accepted globalRow,
      lowerGlobal_mutableSnapshotGraphs_of_accepted accepted globalRow⟩

theorem lower_checkCfg_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ()) :
    checkAll (lower module).infos (fun info => checkCfg info.label info.f info.vt) = .ok () :=
  lower_checkCfg_of_accepted_source_certificates accepted (lower_sourceCfgCertificates_of_accepted accepted)

theorem lower_cfgStages_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ()) :
    checkAll (lower module).infos (fun info => checkCfg info.label info.f info.vt) = .ok () ∧
      checkUnreachable (lower module) = .ok () :=
  lower_cfgStages_of_accepted_source_certificates accepted (lower_sourceCfgCertificates_of_accepted accepted)

end Goose.Lower.Validation
