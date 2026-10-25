import Goose.Evidence.TypingMetadata
import Goose.Lower.Validation.ValueTypeReconstructionEmitted

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ownerLiteralRow_of_source_graphs
    {module : GIR.Module} {func : Func} {le : LEnv} {state : LS}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs)
    (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {value : ValueId} {ty : Ty} {values : List ValueId}
    (literal : Inst.def value (.arrLit ty values) ∈ block.insts) :
    (func.valueTypes module)[value]? = some (some (.data ty)) := by
  have retained := valueTypes_eq_retained_of_source_graphs builder blocks slots globals sigs structs profile graphs
  rw [blocks, finishBlocks, Array.toList_map] at blockMember
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp blockMember
  have definition : Inst.def value (.arrLit ty values) ∈ state.insts :=
    List.mem_flatMap.mpr ⟨source, sourceMember, literal⟩
  have initialPresent : EmittedTypesPresent initState := by
    intro value bound
    change value < 0 at bound
    exact (Nat.not_lt_zero _ bound).elim
  obtain ⟨site, current, trace, checkpoint, extension, live, fresh, typed, recorded, prefixTypes⟩ :=
    (builder.sites value (.arrLit ty values) definition).operation initialPresent
  obtain ⟨element, shape, operands, count, capacity, resultType⟩ := arrLit_metadata typed
  rw [retained]
  simpa only [resultType] using recorded

theorem ownerLiteralRows_of_source_graphs
    {module : GIR.Module} {func : Func} {le : LEnv} {state : LS}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs)
    (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state) :
    ∀ block ∈ func.blocks.toList, ∀ value ty values,
      Inst.def value (.arrLit ty values) ∈ block.insts → isLiteralRunType ty = true →
        (func.valueTypes module)[value]? = some (some (.data ty)) := by
  intro block blockMember value ty values literal runType
  exact ownerLiteralRow_of_source_graphs builder blocks slots globals sigs structs profile graphs
    blockMember literal

end Goose.Lower.Validation
