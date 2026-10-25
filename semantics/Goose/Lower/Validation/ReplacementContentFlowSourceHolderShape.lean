import Goose.Core.DeclarativeTables
import Goose.Lower.Validation.ReplacementContentFlowSourceShape

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

private theorem refSlice_not_storable (type : Ty) (reference : type.isRefSlice = true) :
    type.storable = false := by
  cases type <;> simp_all [Ty.isRefSlice]
  case ref mu target => cases target <;> simp_all [Ty.isRefSlice, Ty.storable, Ty.refTarget]

private theorem readable_not_refSlice (type : Ty) (readable : type.readable = true) :
    type.isRefSlice = false := by
  cases type <;> simp_all [Ty.isRefSlice]
  case ref mu target => cases target <;> simp_all [Ty.isRefSlice, Ty.readable, Ty.refTarget]

theorem accepted_refSlice_variable_parameter {module : Core.Module} {ctx : Context}
    {impl : Impl} {slot : VarId} {localVar : LocalVar}
    (accepted : Core.validate module = .ok ())
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (variableRow : impl.vars[slot]? = some localVar)
    (reference : localVar.ty.isRefSlice = true) :
    ∃ parameter, impl.params[slot]? = some parameter ∧ parameter.var = slot ∧ parameter.mode = .byRef := by
  have tables := (Core.validate_declarativeTables module accepted).implementations impl
    (Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨ctx.impl, implementationRow⟩))
  rcases tables.variables slot localVar variableRow with stored | ⟨_, parameter⟩
  · rw [refSlice_not_storable localVar.ty reference] at stored
    cases stored
  · exact parameter

theorem accepted_context_results_not_refSlice {module : Core.Module} {ctx : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    ∀ type ∈ (lowerContextAt module ctx impl).results, type.isRefSlice = false := by
  have tables := (Core.validate_declarativeTables module accepted).implementations impl
    (Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨ctx.impl, implementationRow⟩))
  intro type member
  apply readable_not_refSlice
  exact (tables.results type member).1

#print axioms accepted_refSlice_variable_parameter
#print axioms accepted_context_results_not_refSlice

end Goose.Lower.Validation.ReplacementContentFlowSource
