import Goose.Lower.Validation.ValidationTypedModuleTables

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitted_definition_final_typed {module : GIR.Module} {func : Func} {le : LEnv} {state : LS}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks) (slots : func.slots = le.slots)
    (globals : module.globals.map (fun global => (global.ty, global.kind)) = le.globals)
    (sigs : module.funcs.map (fun function => (function.params, function.results)) = le.sigs)
    (structs : module.structs = le.mod.structs) (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    {value : ValueId} {op : Op} (definition : Inst.def value op ∈ state.insts) :
    checkInstTypes func { module.tyEnv func with vals := func.valueTypes module }
      (func.valueTypes module) (.def value op) = .ok () := by
  have tables := valueTypes_eq_retained_of_source_graphs builder blocks slots globals sigs structs profile graphs
  have count : func.numValues = state.vals.size := by
    rw [Func.numValues_eq_definition_count, blocks, finishBlocks_defs]
    exact builder.checkpoint.dense.length
  have present : EmittedTypesPresent state := builder.present (by
    intro candidate bound
    exact (Nat.not_lt_zero _ bound).elim)
  have recorded : ∀ candidate, candidate < state.vals.size →
      state.vals[candidate]? = some (some (emittedValueType state candidate)) := by
    intro candidate bound
    obtain ⟨type, row⟩ := present candidate bound
    simp only [emittedValueType, row, Option.getD_some]
  have extended : ExtT state func.blocks := by
    rw [blocks]
    refine ⟨by simp [finishBlocks], ?_⟩
    intro index block row
    refine ⟨⟨block.params, block.insts.toList⟩, ?_, rfl, [], by simp⟩
    simp [finishBlocks, Array.getElem?_map, row]
  obtain ⟨site, current, trace, checkpoint, grows, live, fresh, typed, prefixTypes, authority⟩ :=
    reconstructionEmissionSite_of_source_graph builder graphs definition
  have valueBound : value < func.numValues := by
    rw [count]
    apply builder.checkpoint.dense.mem_lt
    obtain ⟨block, blockMember, instruction⟩ := List.mem_flatMap.mp definition
    exact List.mem_flatMap.mpr ⟨block, blockMember, List.mem_append_right _
      (List.mem_filterMap.mpr ⟨.def value op, instruction, rfl⟩)⟩
  have ready := reconstructionReady_of_source_emission slots globals sigs structs profile
    checkpoint.dense (extended.of_ext grows) checkpoint.operands.uses fresh valueBound
    prefixTypes typed (builder.checkpoint.operands.definitions value op definition) authority
  have front : ReconstructionRankPrefix func id (emittedValueType state) state.vals value := by
    intro candidate bound _
    exact recorded candidate (by rwa [← count])
  have successful := ready state.vals state.vals count.symm count.symm front front
  have environment : { module.tyEnv func with vals := state.vals } =
      reconstructionEnv module func state.vals state.vals := by
    unfold GIR.Module.tyEnv
    rw [tables]
    rfl
  rw [tables]
  simp only [checkInstTypes, environment, successful, bind, Except.bind]
  simp [recorded value (by rwa [← count]), pure, Except.pure]

private theorem finished_definition {func : Func} {state : LS}
    (blocks : func.blocks = finishBlocks state.blocks) {block : GIR.Block}
    (blockMember : block ∈ func.blocks.toList) {value : ValueId} {op : Op}
    (instruction : Inst.def value op ∈ block.insts) : Inst.def value op ∈ state.insts := by
  rw [blocks, finishBlocks, Array.toList_map] at blockMember
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp blockMember
  exact List.mem_flatMap.mpr ⟨original, member, instruction⟩

theorem lowerImpl_definition_typed_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) {block : GIR.Block}
    (blockMember : block ∈ (lowerImpl module impl).blocks.toList) {value : ValueId} {op : Op}
    (instruction : Inst.def value op ∈ block.insts) :
    checkInstTypes (lowerImpl module impl)
      { (lower module).tyEnv (lowerImpl module impl) with vals := (lowerImpl module impl).valueTypes (lower module) }
      ((lowerImpl module impl).valueTypes (lower module)) (.def value op) = .ok () :=
  emitted_definition_final_typed (lowerImpl_emittedBuilder_of_accepted accepted row)
    (cfg_impl_blocks module impl) rfl (lower_globalTypeTables module) (lower_signatureTables module) rfl rfl
    (lowerImpl_mutableSnapshotGraphs_of_accepted accepted row)
    (finished_definition (cfg_impl_blocks module impl) blockMember instruction)

theorem lowerContext_definition_typed_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {context : Context} {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) {block : GIR.Block}
    (blockMember : block ∈ (lowerContextAt module context impl).blocks.toList) {value : ValueId} {op : Op}
    (instruction : Inst.def value op ∈ block.insts) :
    checkInstTypes (lowerContextAt module context impl)
      { (lower module).tyEnv (lowerContextAt module context impl) with
        vals := (lowerContextAt module context impl).valueTypes (lower module) }
      ((lowerContextAt module context impl).valueTypes (lower module)) (.def value op) = .ok () :=
  emitted_definition_final_typed (lowerImpl_emittedBuilder_of_accepted accepted row)
    (cfg_context_blocks module context impl) rfl (lower_globalTypeTables module) (lower_signatureTables module) rfl rfl
    (lowerContext_mutableSnapshotGraphs_of_accepted accepted row)
    (finished_definition (cfg_context_blocks module context impl) blockMember instruction)

theorem lowerGlobal_definition_typed_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : Nat}
    (row : module.globals[index]? = some global) {block : GIR.Block}
    (blockMember : block ∈ (lowerGlobal module global).init.blocks.toList) {value : ValueId} {op : Op}
    (instruction : Inst.def value op ∈ block.insts) :
    checkInstTypes (lowerGlobal module global).init
      { (lower module).tyEnv (lowerGlobal module global).init with
        vals := (lowerGlobal module global).init.valueTypes (lower module) }
      ((lowerGlobal module global).init.valueTypes (lower module)) (.def value op) = .ok () :=
  emitted_definition_final_typed (lowerGlobal_emittedBuilder_of_accepted accepted row)
    (cfg_global_blocks module global) rfl (lower_globalTypeTables module) (lower_signatureTables module) rfl rfl
    (lowerGlobal_mutableSnapshotGraphs_of_accepted accepted row)
    (finished_definition (cfg_global_blocks module global) blockMember instruction)

end Goose.Lower.Validation
