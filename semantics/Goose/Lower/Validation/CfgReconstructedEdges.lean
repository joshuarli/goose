import Goose.Lower.Validation.CfgSourceEdgeFunctions
import Goose.Lower.Validation.CfgSourceDominanceFunctions
import Goose.Lower.Validation.CfgEdgesFinish
import Goose.Lower.Validation.ValueTypeReconstructionEmitted

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerImpl_cfgFacts_of_source_certificates {module : Core.Module} {impl : Core.Impl}
    {type : Ty} {finish : Nat}
    (typed : Core.tyBlock (implEnv module impl) [] impl.body impl.params.size = .ok (type, finish))
    (builder : EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState (cfg_implState module impl))
    (graphs : MutableSnapshotGraphs (lower module) (lowerImpl module impl) (cfg_implState module impl)) :
    CfgFacts (lowerImpl module impl) ((lowerImpl module impl).valueTypes (lower module)) := by
  exact cfgFacts_of_builderEdges (lowerImpl_cfgStructure module impl) (lowerImpl_builderEdges typed)
    (cfg_impl_blocks module impl)
    (lowerImpl_valueTypes_eq_retained builder (cfg_impl_blocks module impl) graphs)
    (lowerImpl_dominatingUses module impl)

theorem lowerContextAt_cfgFacts_of_source_certificates {module : Core.Module} {context : Context} {impl : Core.Impl}
    {type : Ty} {finish : Nat}
    (typed : Core.tyBlock (implEnv module impl) [] impl.body impl.params.size = .ok (type, finish))
    (builder : EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState (cfg_implState module impl))
    (graphs : MutableSnapshotGraphs (lower module) (lowerContextAt module context impl) (cfg_implState module impl)) :
    CfgFacts (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) := by
  exact cfgFacts_of_builderEdges (lowerContextAt_cfgStructure module context impl) (lowerImpl_builderEdges typed)
    (cfg_context_blocks module context impl)
    (lowerContextAt_valueTypes_eq_retained builder (cfg_context_blocks module context impl) graphs)
    (lowerContextAt_dominatingUses module context impl)

theorem lowerGlobal_cfgFacts_of_source_certificates {module : Core.Module} {global : Core.Global}
    {index finish : Nat}
    (typed : Core.tyExpr (initEnv module index) global.init 0 = .ok (global.ty, finish))
    (builder : EmittedBuilder (lowerEnv module #[] [global.ty]) initState (cfg_globalState module global))
    (graphs : MutableSnapshotGraphs (lower module) (lowerGlobal module global).init (cfg_globalState module global)) :
    CfgFacts (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) := by
  exact cfgFacts_of_builderEdges (lowerGlobal_cfgStructure module global) (lowerGlobal_builderEdges typed)
    (cfg_global_blocks module global)
    (lowerGlobal_valueTypes_eq_retained builder (cfg_global_blocks module global) graphs)
    (lowerGlobal_dominatingUses module global)

theorem lowerImpl_checkCfg_of_accepted_source_certificates {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl)
    (builder : EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState (cfg_implState module impl))
    (graphs : MutableSnapshotGraphs (lower module) (lowerImpl module impl) (cfg_implState module impl))
    (label : String) :
    checkCfg label (lowerImpl module impl) ((lowerImpl module impl).valueTypes (lower module)) = .ok () := by
  obtain ⟨type, finish, typed, _⟩ := ((validate_modOk module accepted).impl index impl row).body
  exact cfgFacts_checked (lowerImpl_cfgFacts_of_source_certificates typed builder graphs) label

theorem lowerContextAt_checkCfg_of_accepted_source_certificates {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {context : Context} {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl)
    (builder : EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState (cfg_implState module impl))
    (graphs : MutableSnapshotGraphs (lower module) (lowerContextAt module context impl) (cfg_implState module impl))
    (label : String) :
    checkCfg label (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) = .ok () := by
  obtain ⟨type, finish, typed, _⟩ := ((validate_modOk module accepted).impl index impl row).body
  exact cfgFacts_checked (lowerContextAt_cfgFacts_of_source_certificates typed builder graphs) label

theorem lowerGlobal_checkCfg_of_accepted_source_certificates {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : Nat}
    (row : module.globals[index]? = some global)
    (builder : EmittedBuilder (lowerEnv module #[] [global.ty]) initState (cfg_globalState module global))
    (graphs : MutableSnapshotGraphs (lower module) (lowerGlobal module global).init (cfg_globalState module global))
    (label : String) :
    checkCfg label (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) = .ok () := by
  obtain ⟨finish, typed⟩ := ((validate_modOk module accepted).glob index global row).init
  exact cfgFacts_checked (lowerGlobal_cfgFacts_of_source_certificates typed builder graphs) label

end Goose.Lower.Validation
