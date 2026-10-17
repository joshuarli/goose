import Goose.GIR.ReplacementContentFlowProofsSupportStart
import Goose.Lower.Validation.ReplacementContentFlowSourceAnnotations
import Goose.Lower.Validation.ReplacementContentFlowSourceTypes
import Goose.Lower.Validation.ValidationTypedModuleEntry

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem addressesBounded_of_definitionTypes {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)}
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      (op.resultTy { module.tyEnv func with vals := types }).toOption.any
        (fun type => types[value]? == some (some type)) = true) :
    FunctionAddressesBounded module func := by
  constructor
  · intro block member inst instruction value slot identity
    subst inst
    have checked := definitions block member value (.slotAddr slot) instruction
    cases typed : (Op.slotAddr slot).resultTy { module.tyEnv func with vals := types } with
    | error message => simp [typed, Except.toOption] at checked
    | ok type => exact slotAddr_inBounds _ slot type typed
  · intro block member inst instruction value global identity
    subst inst
    have checked := definitions block member value (.globalAddr global) instruction
    cases typed : (Op.globalAddr global).resultTy { module.tyEnv func with vals := types } with
    | error message => simp [typed, Except.toOption] at checked
    | ok type =>
      have bounded := globalAddr_inBounds _ global type typed
      change global < (module.globals.map (fun item => (item.ty, item.kind))).size at bounded
      simpa only [Array.size_map] using bounded

theorem accepted_context_addressesBounded {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    FunctionAddressesBounded (lower module) (lowerContextAt module ctx impl) := by
  apply addressesBounded_of_definitionTypes
  intro block member value op instruction
  exact accepted_context_definition_type accepted contextRow implementationRow member instruction

theorem accepted_global_addressesBounded {module : Core.Module} {index : GlobalId}
    {global : Core.Global} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global) :
    FunctionAddressesBounded (lower module) (lowerGlobal module global).init := by
  apply addressesBounded_of_definitionTypes
  intro block member value op instruction
  exact accepted_global_definition_type accepted globalRow member instruction

theorem accepted_function_addressesBounded {module : Core.Module} {index : FnId} {func : Func}
    (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some func) :
    FunctionAddressesBounded (lower module) func := by
  obtain ⟨ctx, impl, contextRow, implementationRow, rfl⟩ :=
    accepted_function_context accepted functionRow
  exact accepted_context_addressesBounded accepted contextRow implementationRow

theorem accepted_function_entry_length {module : Core.Module} {index : FnId} {func : Func}
    {entry : GIR.Block} (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some func)
    (entryRow : func.blocks[0]? = some entry) : entry.params.length ≤ func.params.length := by
  obtain ⟨ctx, impl, contextRow, implementationRow, rfl⟩ :=
    accepted_function_context accepted functionRow
  obtain ⟨actual, row, types⟩ := lowerContext_entry_types module ctx impl
  have same : actual = entry := Option.some.inj (row.symm.trans entryRow)
  subst actual
  have arity := congrArg List.length types
  simp only [List.length_map] at arity
  exact Nat.le_of_eq arity

theorem accepted_module_close_finite {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    ∃ states,
      close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states ∧
      ModuleFinite (lower module) states ∧
      moduleRound (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) states = states := by
  apply close_finite
  · intro index func row
    exact accepted_function_annotationsValid accepted row
  · intro index func row entry entryRow
    exact accepted_function_entry_length accepted row entryRow
  · intro index func row
    exact accepted_function_addressesBounded accepted row

#print axioms accepted_context_addressesBounded
#print axioms accepted_global_addressesBounded
#print axioms accepted_function_addressesBounded
#print axioms accepted_function_entry_length
#print axioms accepted_module_close_finite

end Goose.Lower.Validation.ReplacementContentFlowSource
