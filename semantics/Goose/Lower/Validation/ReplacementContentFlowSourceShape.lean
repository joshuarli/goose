import Goose.Lower.ContextLowering
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
  simp [lowerContextAt, lowerImpl, empty, results]

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

#print axioms accepted_entry_shape
#print axioms actual_context_checked

end Goose.Lower.Validation.ReplacementContentFlowSource
