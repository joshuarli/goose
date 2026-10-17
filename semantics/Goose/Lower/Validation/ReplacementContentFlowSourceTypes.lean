import Goose.Lower.Validation.ReplacementContentFlowSourceShape
import Goose.Lower.Validation.ValidationTypedModuleDefinitions

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

private theorem definition_type_of_checked {func : Func} {env : TyEnv}
    {types : Array (Option VTy)} {value : ValueId} {op : Op}
    (checked : checkInstTypes func env types (.def value op) = .ok ()) :
    (op.resultTy env).toOption.any (fun type => types[value]? == some (some type)) = true := by
  cases typed : op.resultTy env with
  | error message => simp [checkInstTypes, typed, bind, Except.bind] at checked
  | ok type =>
    simp only [checkInstTypes, typed, bind, Except.bind] at checked
    split at checked
    all_goals simp_all [throw, pure, Except.toOption]

theorem accepted_context_definition_type {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {block : GIR.Block} {value : ValueId} {op : Op}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (blockMember : block ∈ (lowerContextAt module ctx impl).blocks.toList)
    (instructionMember : Inst.def value op ∈ block.insts) :
    let func := lowerContextAt module ctx impl
    let types := func.valueTypes (lower module)
    (op.resultTy { (lower module).tyEnv func with vals := types }).toOption.any
      (fun type => types[value]? == some (some type)) = true := by
  exact definition_type_of_checked
    (lowerContext_definition_typed_of_accepted accepted implementationRow blockMember instructionMember)

theorem accepted_global_definition_type {module : Core.Module} {index : GlobalId}
    {global : Core.Global} {block : GIR.Block} {value : ValueId} {op : Op}
    (accepted : Core.validate module = .ok ()) (globalRow : module.globals[index]? = some global)
    (blockMember : block ∈ (lowerGlobal module global).init.blocks.toList)
    (instructionMember : Inst.def value op ∈ block.insts) :
    let func := (lowerGlobal module global).init
    let types := func.valueTypes (lower module)
    (op.resultTy { (lower module).tyEnv func with vals := types }).toOption.any
      (fun type => types[value]? == some (some type)) = true := by
  exact definition_type_of_checked
    (lowerGlobal_definition_typed_of_accepted accepted globalRow blockMember instructionMember)

private theorem finished_parameters_typed {module : GIR.Module} {func : Func} {state : LS}
    (parameters : EmittedParametersTyped state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (types : func.valueTypes module = state.vals)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {value : ValueId} {type : VTy} (parameterMember : (value, type) ∈ block.params) :
    (func.valueTypes module)[value]? = some (some type) := by
  rw [blocks, finishBlocks, Array.toList_map] at blockMember
  obtain ⟨body, member, identity⟩ := List.mem_map.mp blockMember
  subst block
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  rw [types]
  exact parameters index body row value type parameterMember

theorem accepted_context_parameter_type {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {block : GIR.Block} {value : ValueId} {type : VTy}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (blockMember : block ∈ (lowerContextAt module ctx impl).blocks.toList)
    (parameterMember : (value, type) ∈ block.params) :
    ((lowerContextAt module ctx impl).valueTypes (lower module))[value]? = some (some type) := by
  exact finished_parameters_typed
    (lowerImpl_emittedBuilder_of_accepted accepted implementationRow).checkpoint.parameters
    (cfg_context_blocks module ctx impl)
    (lowerContext_valueTypes_of_accepted accepted implementationRow) blockMember parameterMember

theorem accepted_global_parameter_type {module : Core.Module} {index : GlobalId}
    {global : Core.Global} {block : GIR.Block} {value : ValueId} {type : VTy}
    (accepted : Core.validate module = .ok ()) (globalRow : module.globals[index]? = some global)
    (blockMember : block ∈ (lowerGlobal module global).init.blocks.toList)
    (parameterMember : (value, type) ∈ block.params) :
    ((lowerGlobal module global).init.valueTypes (lower module))[value]? = some (some type) := by
  exact finished_parameters_typed
    (lowerGlobal_emittedBuilder_of_accepted accepted globalRow).checkpoint.parameters
    (cfg_global_blocks module global)
    (lowerGlobal_valueTypes_of_accepted accepted globalRow) blockMember parameterMember

#print axioms accepted_context_parameter_type
#print axioms accepted_global_parameter_type
#print axioms accepted_context_definition_type
#print axioms accepted_global_definition_type

end Goose.Lower.Validation.ReplacementContentFlowSource
