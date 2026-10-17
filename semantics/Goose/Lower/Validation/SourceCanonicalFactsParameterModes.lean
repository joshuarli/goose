import Goose.Lower.Frag
import Goose.Lower.Validation.SummaryPreservationVariableShape

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerContext_refSlice_parameter_of_accepted {module : Core.Module}
    {context : Context} {impl : Impl} {index : Nat}
    (accepted : Core.validate module = .ok ())
    (implAt : module.impls[context.impl]? = some impl)
    (reference : ((lowerContextAt module context impl).params[index]?).any Ty.isRefSlice = true) :
    ∃ parameter localVar, impl.params[index]? = some parameter ∧
      impl.vars[parameter.var]? = some localVar ∧ parameter.mode = .byRef ∧ localVar.ty.isRefSlice = true := by
  change ((impl.params.toList.map fun parameter => tyOfVar impl parameter.var)[index]?).any Ty.isRefSlice = true at reference
  rw [List.getElem?_map, Array.getElem?_toList] at reference
  cases parameterAt : impl.params[index]? with
  | none => simp [parameterAt] at reference
  | some parameter =>
    obtain ⟨aligned, localVar, variableAt, _, _⟩ :=
      (Core.Sound.validate_modOk module accepted).impl context.impl impl implAt |>.params index parameter parameterAt
    have localReference : localVar.ty.isRefSlice = true := by
      simpa [parameterAt, tyOfVar, aligned, variableAt] using reference
    obtain ⟨formal, formalAt, _, mode⟩ :=
      SummaryPreservation.accepted_refSlice_parameter accepted implAt variableAt localReference
    have same : formal = parameter := Option.some.inj (formalAt.symm.trans parameterAt)
    exact ⟨parameter, localVar, rfl, aligned ▸ variableAt, same ▸ mode, localReference⟩

#print axioms lowerContext_refSlice_parameter_of_accepted


end Goose.Lower.Validation
