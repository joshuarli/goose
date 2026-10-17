import Goose.Lower.Validation.AdmittedSourceCallsContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLedger

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem ReplacementContentFlowSource.CallOccurrence.parameter_contracts
    {module : Core.Module} {context : ContextId} {ctx : Context} {impl : Impl}
    {env : PEnv} {root : DemandNode} {func : Func} {provenance upper : Prov}
    {value : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (accepted : Core.validate module = .ok ())
    (contextFound : module.contexts[context]? = some ctx)
    (implementationFound : module.impls[ctx.impl]? = some impl)
    (environment : env.mod = module)
    (occurrence : CallOccurrence env root func upper value context arguments origin)
    (arity : arguments.length = impl.params.size)
    (below : ∀ argument, rootsAt provenance.vals argument ⊆ rootsAt upper.vals argument) :
    ∀ index, GIR.RootsRefine func (mapRawContentRoots provenance arguments [.param index])
      (mapRawContentRoots provenance arguments ((lowerContextAt module ctx impl).parameterRoots index)) := by
  obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, before, argumentRoots, argumentsAfter,
    resultRoots, after, access, originEq, node, argumentsReplay, contentChecked, callReplay,
    valueBound, valueRefined, argumentOrigins, physicalArguments⟩ := occurrence
  apply AdmittedSourceCalls.accepted_call_parameter_contracts accepted contextFound
    implementationFound ((congrArg AccessEnv.mod access).trans environment) arity callReplay
  intro index argument argumentFound
  obtain ⟨bound, roots, rootsFound, refined⟩ := argumentOrigins index argument argumentFound
  exact ⟨roots, rootsFound, refined.actual_mono (below argument)⟩

end Goose.Lower.Validation
