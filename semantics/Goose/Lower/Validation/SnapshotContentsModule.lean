import Goose.Lower.Validation.SnapshotContentsSourceDriver
import Goose.Lower.Validation.SnapshotContentsFunctions

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerImpl_snapshotSourceTrace_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) :
    SnapshotSourceTrace (lowerEnv module impl.vars impl.results.toList) 0
      (cfg_implState module impl) (cfg_implState module impl) := by
  obtain ⟨type, finish, typed, _⟩ := ((validate_modOk module accepted).impl index impl row).body
  exact lowerImpl_snapshotSourceTrace typed (snapshot_source_block impl.body (implEnv module impl) impl.results.toList)

theorem lowerGlobal_snapshotSourceTrace_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : Nat}
    (row : module.globals[index]? = some global) :
    SnapshotSourceTrace (lowerEnv module #[] [global.ty]) 0
      (cfg_globalState module global) (cfg_globalState module global) := by
  obtain ⟨finish, typed⟩ := ((validate_modOk module accepted).glob index global row).init
  exact lowerGlobal_snapshotSourceTrace typed
    (snapshot_source_expression global.init (initEnv module index) [global.ty])

theorem lowerImpl_mutableSnapshotGraphs_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) :
    MutableSnapshotGraphs (lower module) (lowerImpl module impl) (cfg_implState module impl) :=
  lowerImpl_mutableSnapshotGraphs (lowerImpl_snapshotSourceTrace_of_accepted accepted row)

theorem lowerContext_mutableSnapshotGraphs_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {context : Context} {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) :
    MutableSnapshotGraphs (lower module) (lowerContextAt module context impl) (cfg_implState module impl) :=
  lowerContext_mutableSnapshotGraphs (lowerImpl_snapshotSourceTrace_of_accepted accepted row)

theorem lowerGlobal_mutableSnapshotGraphs_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : Nat}
    (row : module.globals[index]? = some global) :
    MutableSnapshotGraphs (lower module) (lowerGlobal module global).init (cfg_globalState module global) :=
  lowerGlobal_mutableSnapshotGraphs (lowerGlobal_snapshotSourceTrace_of_accepted accepted row)

end Goose.Lower.Validation
