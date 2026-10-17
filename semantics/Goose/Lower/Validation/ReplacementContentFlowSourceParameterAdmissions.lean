import Goose.Lower.Validation.ReplacementContentFlowSourceAdmittedInputs

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model
open SummaryPreservation

theorem accepted_parameter_query_permitted {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {caller : Func} {sourceArgs : List (List RootRef)}
    {actual : List RootRef} {index : Nat}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (bounded : index < impl.params.size)
    (checked : checkArgRoots impl ctx sourceArgs index = .ok ())
    (within : actual ⊆ (sourceArgs[index]?.getD []).flatMap caller.expandParameterRoot) :
    let declared := (lowerContextAt module ctx impl).parameterRoots index
    (declared.contains (.param index) || actual.all (fun root => match root with
      | .global global => declared.contains (.global global)
      | .local _ | .param _ => declared.contains (.param index))) = true := by
  dsimp only
  by_cases self : RootRef.param index ∈ (lowerContextAt module ctx impl).parameterRoots index
  · have present : ((lowerContextAt module ctx impl).parameterRoots index).contains (.param index) = true :=
      List.contains_iff_mem.mpr self
    simp only [present, Bool.true_or]
  · have permitted := accepted_call_argument_globals (caller := caller) accepted contextRow implementationRow bounded checked self
    have closed := lowerContextAt_parameterRoots_closed accepted contextRow implementationRow
    apply Bool.or_eq_true_iff.mpr
    right
    apply List.all_eq_true.mpr
    intro root member
    have rootPermitted := permitted root (within member)
    rcases closed index root rootPermitted with own | ⟨global, identity⟩
    · exact False.elim (self (own ▸ rootPermitted))
    · subst root
      exact List.contains_iff_mem.mpr rootPermitted

#print axioms accepted_parameter_query_permitted

end Goose.Lower.Validation.ReplacementContentFlowSource
