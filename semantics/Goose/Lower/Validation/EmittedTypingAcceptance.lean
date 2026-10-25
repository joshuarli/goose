import Goose.Lower.Validation.EmittedTypingFunctions

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem EmittedBuilder.finishedSite {le : LEnv} {initial state : LS}
    (builder : EmittedBuilder le initial state) {func : Func}
    (blocks : func.blocks = finishBlocks state.blocks) {block : GIR.Block}
    (blockMember : block ∈ func.blocks.toList) {value : ValueId} {op : Op}
    (instructionMember : Inst.def value op ∈ block.insts) :
    EmittedCheckedSite le initial state value op := by
  rw [blocks, finishBlocks, Array.toList_map] at blockMember
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp blockMember
  exact builder.sites value op (List.mem_flatMap.mpr ⟨original, originalMember, instructionMember⟩)

theorem lowerImpl_emittedSite_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {impl : Core.Impl} {index : Nat} (row : module.impls[index]? = some impl)
    {block : GIR.Block} (blockMember : block ∈ (lowerImpl module impl).blocks.toList)
    {value : ValueId} {op : Op} (instructionMember : Inst.def value op ∈ block.insts) :
    EmittedCheckedSite (lowerEnv module impl.vars impl.results.toList) initState
      (cfg_implState module impl) value op :=
  (lowerImpl_emittedBuilder_of_accepted accepted row).finishedSite
    (cfg_impl_blocks module impl) blockMember instructionMember

theorem lowerContextAt_emittedSite_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {context : Context} {contextIndex : Nat} (row : module.contexts[contextIndex]? = some context)
    {impl : Core.Impl} (implRow : module.impls[context.impl]? = some impl)
    {block : GIR.Block} (blockMember : block ∈ (lowerContextAt module context impl).blocks.toList)
    {value : ValueId} {op : Op} (instructionMember : Inst.def value op ∈ block.insts) :
    EmittedCheckedSite (lowerEnv module impl.vars impl.results.toList) initState
      (cfg_implState module impl) value op := by
  obtain ⟨found, foundRow, checked⟩ := (validate_modOk module accepted).ctx contextIndex context row
  have same : found = impl := Option.some.inj (foundRow.symm.trans implRow)
  subst found
  obtain ⟨type, finish, typed, rest⟩ := ((validate_modOk module accepted).impl context.impl impl implRow).body
  exact (lowerImpl_emittedBuilder typed).finishedSite (cfg_context_blocks module context impl) blockMember instructionMember

theorem lowerGlobal_emittedSite_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {global : Core.Global} {index : Nat} (row : module.globals[index]? = some global)
    {block : GIR.Block} (blockMember : block ∈ (lowerGlobal module global).init.blocks.toList)
    {value : ValueId} {op : Op} (instructionMember : Inst.def value op ∈ block.insts) :
    EmittedCheckedSite (lowerEnv module #[] [global.ty]) initState
      (cfg_globalState module global) value op :=
  (lowerGlobal_emittedBuilder_of_accepted accepted row).finishedSite
    (cfg_global_blocks module global) blockMember instructionMember

end Goose.Lower.Validation
