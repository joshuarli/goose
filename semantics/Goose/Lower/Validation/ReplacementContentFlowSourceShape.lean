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

theorem accepted_context_return_seed {module : Core.Module} {index : ContextId} {ctx : Context}
    {impl : Impl} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[index]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    ∃ atoms, declaredReturn (lowerContextAt module ctx impl) = .known atoms := by
  have checked := actual_context_checked accepted contextRow implementationRow
  obtain ⟨bodyType, next, typed, shape⟩ :=
    ((Core.Sound.validate_modOk module accepted).impl ctx.impl impl implementationRow).body
  rcases shape with ⟨empty, _⟩ | ⟨type, singleton, _⟩
  · exact ⟨[], by simp [declaredReturn, lowerContextAt, lowerImpl, empty]⟩
  · have bound : 0 < impl.results.size := by
      have lengths := congrArg List.length singleton
      have size : impl.results.size = 1 := by simpa using lengths
      omega
    obtain ⟨roots, row⟩ := Option.isSome_iff_exists.mp
      (show ((lowerContextRootInfo ctx impl).results[0]?).isSome = true by
        simp [SummaryPreservation.lowerContextRootInfo_result_eq bound])
    by_cases reference : type.isRefLike = true
    · refine ⟨roots.map (fun root => match root with
        | .local slot => Atom.local slot
        | .global global => Atom.global global
        | .param parameter => Atom.param parameter), ?_⟩
      simp only [declaredReturn, lowerContextAt, lowerImpl, singleton, reference, ite_true]
      rw [row]
      rfl
    · refine ⟨[], ?_⟩
      simp [declaredReturn, lowerContextAt, lowerImpl, singleton, reference]

theorem accepted_global_return_seed {module : Core.Module} {index : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ()) (globalRow : module.globals[index]? = some global) :
    declaredReturn (lowerGlobal module global).init = .known [] := by
  have checked := (Core.Sound.validate_modOk module accepted).glob index global globalRow
  simp [declaredReturn, lowerGlobal, checked.ty.2]

#print axioms accepted_global_return_seed
#print axioms accepted_context_return_seed
#print axioms accepted_entry_shape
#print axioms actual_context_checked

end Goose.Lower.Validation.ReplacementContentFlowSource
