import Goose.Lower.Validation.Evidence
import Goose.Lower.Validation.InterfaceTypes
import Goose.Lower.Validation.Results
import Goose.Lower.Validation.Scopes
import Goose.Lower.Validation.Stages

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lower_preserves_entry_origins_evidence {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    checkEntryAndGlobals (lower module) = .ok () ∧
      (checkAll (lower module).infos fun info =>
        checkOrigins (lower module).profile info.label info.f) = .ok () ∧
      (checkAll (lower module).infos fun info =>
        asCheck .v080 info.label (checkEvidence (lower module) info.f info.vt)) = .ok () :=
  ⟨lower_checkEntryAndGlobals accepted, lower_checkOrigins accepted, lower_checkEvidence module⟩

theorem lowerImpl_scopeParents_of_accepted {module : Core.Module} {index : ImplId} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ()) (lookup : module.impls[index]? = some impl)
    (scope parent : Nat)
    (row : (lowerImpl module impl).scopes[scope]? = some (some parent)) :
    parent < scope :=
  lowerImpl_scopeParents_earlier
    (validate_implementation_checks accepted
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))) scope parent row

theorem lowerGlobal_scopeParents_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (lookup : module.globals[index]? = some global) (scope parent : Nat)
    (row : (lowerGlobal module global).init.scopes[scope]? = some (some parent)) :
    parent < scope :=
  lowerGlobal_scopeParents_earlier (validate_global_checks accepted lookup) scope parent row

end Goose.Lower.Validation
