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

#print axioms accepted_context_definition_type
#print axioms accepted_global_definition_type

end Goose.Lower.Validation.ReplacementContentFlowSource
