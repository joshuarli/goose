import Goose.Lower.Validation.StorageSourceBuilder
import Goose.Lower.Validation.ValueTypeReconstructionEmitted

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageBuilder.checkStorage {module : GIR.Module} {func : Func} {le : LEnv} {state : LS}
    (storage : StorageBuilder le.mod.profile state)
    (blocks : func.blocks = Goose.Lower.finishBlocks state.blocks) (profile : module.profile = le.mod.profile)
    (reconstructed : func.valueTypes module = state.vals) (label : String) :
    checkStorage module label func (func.valueTypes module) = .ok () := by
  rw [reconstructed]
  apply checkStorage_of_rules
  simpa only [profile] using storage.finishBlocks blocks

theorem checkStorage_of_source_graphs {module : GIR.Module} {func : Func} {le : LEnv} {state : LS}
    (storage : StorageBuilder le.mod.profile state) (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = Goose.Lower.finishBlocks state.blocks) (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (signatures : (module.funcs.map fun function => (function.params, function.results)) = le.sigs)
    (structs : module.structs = le.mod.structs) (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state) (label : String) :
    checkStorage module label func (func.valueTypes module) = .ok () :=
  storage.checkStorage blocks profile
    (valueTypes_eq_retained_of_source_graphs builder blocks slots globals signatures structs profile graphs) label

theorem lowerImpl_checkStorage_of_source_graphs {module : Core.Module} {impl : Core.Impl} {state : LS}
    (storage : StorageBuilder module.profile state)
    (builder : EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState state)
    (blocks : (lowerImpl module impl).blocks = Goose.Lower.finishBlocks state.blocks)
    (graphs : MutableSnapshotGraphs (lower module) (lowerImpl module impl) state) (label : String) :
    checkStorage (lower module) label (lowerImpl module impl)
      ((lowerImpl module impl).valueTypes (lower module)) = .ok () :=
  storage.checkStorage (le := lowerEnv module impl.vars impl.results.toList) blocks rfl (lowerImpl_valueTypes_eq_retained builder blocks graphs) label

end Goose.Lower.Validation
