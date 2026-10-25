import Goose.Lower.Validation.RootAnnotationRules
import Goose.Lower.Validation.SourceRootAnnotationCalls
import Goose.Lower.Validation.SourceCallArity
import Goose.Lower.Validation.AdmittedSourceAccepted
import Goose.Lower.Validation.AdmittedRootContentCoverage
import Goose.Lower.Validation.SourceCanonicalFactsObserved
import Goose.Lower.Validation.ReplacementContentFlowSourceShape

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

theorem accepted_context_checkRootAnnotationsOf {module : Core.Module} {context : Context} {impl : Impl}
    {index : ContextId} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    checkRootAnnotationsOf (lower module) (lower module).implTypes
      (resultRoots (lower module) (lower module).implTypes) (lower module).rootCount index = .ok () := by
  have typeRow : (lower module).implTypes[index]?.getD #[] =
      (lowerContextAt module context impl).valueTypes (lower module) := by
    rw [module_implTypes_eq_native]
    simp only [Array.getElem?_map, lower_func_at contextAt implAt, Option.map_some, Option.getD_some]
  obtain ⟨upper, below, occurrences⟩ := accepted_context_instruction_occurrences accepted contextAt implAt
  apply checkRootAnnotationsOf_of_bounds (lower_func_at contextAt implAt)
  · intro root member
    apply accepted_resultRoots_declared accepted contextAt implAt root
    simpa only [module_implTypes_eq_native] using member
  · dsimp only
    rw [typeRow]
    intro block member value function arguments origin called callee calleeAt parameter bound reference
    obtain ⟨calleeContext, calleeImpl, calleeContextAt, calleeImplAt, rfl⟩ :=
      accepted_function_context accepted calleeAt
    have occurrence := (occurrences block member _ called).2.2.1 value function arguments origin rfl
    obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, before, argumentRoots, argumentsAfter,
      resultRoots, after, localAccess, originEq, node, argumentsReplay, contentChecked, callReplay,
      valueBound, valueRefined, argumentOrigins, physicalArguments, trace⟩ := occurrence
    have environment : localEnv.mod = module := congrArg AccessEnv.mod localAccess
    have arity := trace.arity environment calleeContextAt calleeImplAt
    have sourceBound : parameter < calleeImpl.params.size := by
      simpa only [lowerContextAt, lowerImpl, lowerImplFromState, List.length_map, Array.length_toList] using bound
    have nativeBound : parameter < arguments.length := by omega
    let argument := arguments[parameter]
    have argumentAt : arguments[parameter]? = some argument := by simp [argument, nativeBound]
    have sourceReference : (tyOfVar calleeImpl (calleeImpl.params[parameter]'sourceBound).var).isRefLike = true := by
      simpa only [lowerContextAt, lowerImpl, lowerImplFromState, List.getElem_map,
        Array.getElem_toList] using reference
    have sourceOccurrence : CallOccurrence ⟨module, impl, context, []⟩ (.block impl.body)
        (lowerContextAt module context impl) upper value function arguments origin :=
      occurrences block member _ called |>.2.2.1 value function arguments origin rfl
    have checked := sourceOccurrence.argument_checked accepted calleeContextAt calleeImplAt rfl
      sourceBound sourceReference argumentAt (fun {root} member => below.vals argument root member)
    simpa only [List.getElem!_of_getElem? argumentAt] using checked
  · dsimp only
    rw [typeRow]
    intro block member value function arguments origin called callee calleeAt parameter bound reference row found
    obtain ⟨actual, ceiling⟩ := row
    have rowKey : actual = parameter := eq_of_beq (Array.find?_some (p := fun entry : Nat × List RootRef => entry.1 == parameter) (a := (actual, ceiling)) found)
    subst actual
    have rowMember : (parameter, ceiling) ∈ callee.roots.contents.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found)
    apply Func.checkAdmittedRegions_argumentContents_subset
      (accepted_context_checkAdmittedRegions accepted contextAt implAt)
      (lowerContextAt_parameterRoots_closed accepted contextAt implAt) member called calleeAt rowMember
    simpa only [List.getElem?_eq_getElem bound, Option.any_some] using reference
  · dsimp only
    rw [typeRow]
    intro block member value address loaded mutability element typed parameter present reference
    apply lowerContext_canonical_loadObserved_of_accepted accepted contextAt implAt block member value address loaded
      (by simp [valRefLike, typed, VTy.refLike, Ty.isRefLike]) parameter present reference

#print axioms accepted_context_checkRootAnnotationsOf

end Goose.Lower.Validation
