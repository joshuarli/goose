import Goose.Lower.Validation.ValidationStructuralStorage
import Goose.Lower.Validation.SourceSymbolSourceCheck

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure StructuralValidation (module : GIR.Module) : Prop where
  entry : checkEntryAndGlobals module = .ok ()
  symbols : checkAll module.labelled (fun (label, func) => checkSymbols module label func) = .ok ()
  cfg : checkAll module.infos (fun info => checkCfg info.label info.f info.vt) = .ok ()
  unreachable : checkUnreachable module = .ok ()
  storage : checkAll module.infos (fun info => checkStorage module info.label info.f info.vt) = .ok ()
  evidence : checkAll module.infos (fun info => asCheck .v080 info.label (checkEvidence module info.f info.vt)) = .ok ()
  origins : checkAll module.infos (fun info => checkOrigins module.profile info.label info.f) = .ok ()

theorem lower_structuralValidation_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) : StructuralValidation (lower module) :=
  ⟨lower_checkEntryAndGlobals accepted, SourceSymbolSource.lower_checkSymbols accepted,
    lower_checkCfg_of_accepted accepted, lower_checkUnreachable_of_accepted accepted,
    lower_checkStorage_of_accepted accepted, lower_checkEvidence module, lower_checkOrigins accepted⟩

end Goose.Lower.Validation
