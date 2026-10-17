import Goose.Lower.Validation.EmittedTypingFunctions
import Goose.Lower.Validation.SnapshotContentsModule

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerImpl_valueTypes_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) :
    (lowerImpl module impl).valueTypes (lower module) = (cfg_implState module impl).vals :=
  lowerImpl_valueTypes_eq_retained (lowerImpl_emittedBuilder_of_accepted accepted row)
    (cfg_impl_blocks module impl) (lowerImpl_mutableSnapshotGraphs_of_accepted accepted row)

theorem lowerContext_valueTypes_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {context : Context} {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) :
    (lowerContextAt module context impl).valueTypes (lower module) = (cfg_implState module impl).vals :=
  lowerContextAt_valueTypes_eq_retained (lowerImpl_emittedBuilder_of_accepted accepted row)
    (cfg_context_blocks module context impl) (lowerContext_mutableSnapshotGraphs_of_accepted accepted row)

theorem lowerGlobal_valueTypes_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : Nat}
    (row : module.globals[index]? = some global) :
    (lowerGlobal module global).init.valueTypes (lower module) = (cfg_globalState module global).vals :=
  lowerGlobal_valueTypes_eq_retained (lowerGlobal_emittedBuilder_of_accepted accepted row)
    (cfg_global_blocks module global) (lowerGlobal_mutableSnapshotGraphs_of_accepted accepted row)

end Goose.Lower.Validation
