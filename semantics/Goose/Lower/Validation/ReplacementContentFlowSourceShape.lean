import Goose.Lower.ContextLowering
import Goose.GIR.ReplacementContentFlowProofsSupportStart
import Goose.Lower.Validation.ReplacementContentFlowSourceRoots

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_entry_shape {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    ((lower module).funcs[(lower module).entry]?).any
      (fun entry => entry.params.isEmpty && entry.results.isEmpty) = true := by
  obtain ⟨ctx, impl, contextRow, implementationRow, parameters, results⟩ :=
    (Core.Sound.validate_modOk module accepted).entry
  have row := lower_func_at contextRow implementationRow
  change ((lower module).funcs[module.entry]?).any _ = true
  rw [row]
  have empty : impl.params.toList = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using parameters
  simp [lowerContextAt, lowerImpl, lowerImplFromState, empty, results]

theorem actual_context_checked {module : Core.Module} {index : ContextId} {ctx : Context}
    {impl : Impl} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[index]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    Core.Sound.CtxOk module impl ctx := by
  obtain ⟨checked, row, properties⟩ :=
    (Core.Sound.validate_modOk module accepted).ctx index ctx contextRow
  rw [implementationRow] at row
  cases row
  exact properties

theorem accepted_context_return_seed {module : Core.Module} {index : ContextId} {ctx : Context}
    {impl : Impl} {types : Array (Option VTy)} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[index]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    ∃ atoms, (start (lowerContextAt module ctx impl) types).returned = .known atoms :=
  ⟨[], start_returned _ _⟩

theorem accepted_global_return_seed {module : Core.Module} {index : GlobalId} {global : Core.Global}
    {types : Array (Option VTy)}
    (accepted : Core.validate module = .ok ()) (globalRow : module.globals[index]? = some global) :
    (start (lowerGlobal module global).init types).returned = .known [] :=
  start_returned _ _

theorem accepted_function_context {module : Core.Module} {index : FnId} {func : Func}
    (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some func) :
    ∃ ctx impl, module.contexts[index]? = some ctx ∧ module.impls[ctx.impl]? = some impl ∧
      func = lowerContextAt module ctx impl := by
  cases contextRow : module.contexts[index]? with
  | none => simp [lower, Array.getElem?_map, contextRow] at functionRow
  | some ctx =>
    obtain ⟨impl, implementationRow, checked⟩ :=
      (Core.Sound.validate_modOk module accepted).ctx index ctx contextRow
    exact ⟨ctx, impl, rfl, implementationRow,
      Option.some.inj (functionRow.symm.trans (lower_func_at contextRow implementationRow))⟩

theorem accepted_context_parameters {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    (lowerContextAt module ctx impl).params.all Ty.paramOk = true := by
  apply List.all_eq_true.mpr
  intro type member
  change type ∈ impl.params.toList.map (fun param => tyOfVar impl param.var) at member
  obtain ⟨param, paramMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨index, paramRow⟩ := List.mem_iff_getElem?.mp paramMember
  have row : impl.params[index]? = some param := by simpa only [Array.getElem?_toList] using paramRow
  obtain ⟨identity, localVar, variableRow, scope, valid⟩ :=
    ((Core.Sound.validate_modOk module accepted).impl ctx.impl impl implementationRow).params index param row
  simpa only [tyOfVar, identity, variableRow, Option.map_some, Option.getD_some] using valid

#print axioms accepted_context_parameters
#print axioms accepted_function_context
#print axioms accepted_global_return_seed
#print axioms accepted_context_return_seed
#print axioms accepted_entry_shape
#print axioms actual_context_checked

end Goose.Lower.Validation.ReplacementContentFlowSource
