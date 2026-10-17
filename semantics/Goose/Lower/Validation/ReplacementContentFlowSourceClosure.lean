import Goose.GIR.ReplacementContentFlowProofsClosure
import Goose.Lower.Validation.ReplacementContentFlowSourceFinite

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_global_entry_length {module : Core.Module} {global : Core.Global}
    {entry : GIR.Block}
    (entryRow : (lowerGlobal module global).init.blocks[0]? = some entry) :
    entry.params.length ≤ (lowerGlobal module global).init.params.length := by
  obtain ⟨actual, row, types⟩ := lowerGlobal_entry_types module global
  have same : actual = entry := Option.some.inj (row.symm.trans entryRow)
  subst actual
  have arity := congrArg List.length types
  simp only [List.length_map] at arity
  exact Nat.le_of_eq arity

theorem accepted_function_solver_outcome {module : Core.Module} {index : FnId} {func : Func}
    {states : Array State} (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some func)
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states) :
    ∃ result,
      FunctionReachable (lower module) states func (func.valueTypes (lower module))
        (start func (func.valueTypes (lower module))) result ∧
      FunctionFinite (lower module) func result ∧
      round (lower module) states func (func.valueTypes (lower module)) result = result ∧
      closeFunction (lower module) states func (func.valueTypes (lower module)) =
        if check (lower module) func (func.valueTypes (lower module)) result then some result else none := by
  obtain ⟨actual, found, finite, stable⟩ := accepted_module_close_finite accepted
  have same : actual = states := Option.some.inj (found.symm.trans closed)
  subst actual
  exact closeFunction_outcome _ _ _ _ finite.1
    (accepted_function_annotationsValid accepted functionRow)
    (fun entry row => accepted_function_entry_length accepted functionRow row)
    (accepted_function_addressesBounded accepted functionRow)

theorem accepted_global_solver_outcome {module : Core.Module} {index : GlobalId}
    {global : Core.Global} {states : Array State}
    (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states) :
    let func := (lowerGlobal module global).init
    ∃ result, FunctionReachable (lower module) states func (func.valueTypes (lower module))
        (start func (func.valueTypes (lower module))) result ∧
      FunctionFinite (lower module) func result ∧
      round (lower module) states func (func.valueTypes (lower module)) result = result ∧
      closeFunction (lower module) states func (func.valueTypes (lower module)) =
        if check (lower module) func (func.valueTypes (lower module)) result then some result else none := by
  dsimp only
  obtain ⟨actual, found, finite, stable⟩ := accepted_module_close_finite accepted
  have same : actual = states := Option.some.inj (found.symm.trans closed)
  subst actual
  exact closeFunction_outcome _ _ _ _ finite.1
    (accepted_global_annotationsValid accepted globalRow)
    (fun entry row => accepted_global_entry_length row)
    (accepted_global_addressesBounded accepted globalRow)

#print axioms accepted_global_entry_length
#print axioms accepted_function_solver_outcome
#print axioms accepted_global_solver_outcome

end Goose.Lower.Validation.ReplacementContentFlowSource
