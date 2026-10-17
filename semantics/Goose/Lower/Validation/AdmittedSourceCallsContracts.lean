import Goose.Lower.Validation.AdmittedSourceCallsCoverage
import Goose.Lower.Validation.SummaryPreservationArgumentAnnotations

namespace Goose.Lower.Validation.AdmittedSourceCalls

open Goose.Core Goose.GIR

theorem accepted_call_parameter_contracts
    {module : Core.Module} {context : ContextId} {ctx : Context} {impl : Impl}
    {env : PEnv} {func : Func} {provenance : Prov} {arguments : List ValueId}
    {sourceArguments : List (List RootRef)} {before after : RState} {resultRoots : List RootRef}
    (accepted : Core.validate module = .ok ())
    (contextFound : module.contexts[context]? = some ctx)
    (implementationFound : module.impls[ctx.impl]? = some impl)
    (environment : env.mod = module)
    (arity : arguments.length = impl.params.size)
    (source : rpCall env context sourceArguments before = .ok (resultRoots, after))
    (argumentBounds : ∀ (index : Nat) (argument : ValueId), arguments[index]? = some argument →
      ∃ roots, sourceArguments[index]? = some roots ∧
        GIR.RootsRefine func (rootsAt provenance.vals argument) roots) :
    ∀ index, GIR.RootsRefine func (mapRawContentRoots provenance arguments [.param index])
      (mapRawContentRoots provenance arguments ((lowerContextAt module ctx impl).parameterRoots index)) := by
  apply raw_parameter_contracts_of_argument_domains
  intro index argument argumentFound
  have bound : index < impl.params.size := by
    rw [← arity]
    exact (List.getElem?_eq_some_iff.mp argumentFound).1
  obtain ⟨roots, rootsFound, refined⟩ := argumentBounds index argument argumentFound
  have domain := SummaryPreservation.accepted_call_argument_domain accepted contextFound
    implementationFound environment bound source
    (by simpa only [rootsFound, Option.getD_some] using refined)
  exact domain

end Goose.Lower.Validation.AdmittedSourceCalls
