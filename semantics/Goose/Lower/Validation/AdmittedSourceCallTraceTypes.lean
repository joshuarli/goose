import Goose.Lower.Validation.AdmittedSourceCallArgumentTypes
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceCallTrace
import Goose.Lower.Validation.SummaryPreservationVariableShape
import Goose.Lower.Validation.InterfaceTypes

namespace Goose.Lower.Validation.AdmittedSourceCalls

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource

theorem trace_refSlice_local_argument {module : Core.Module} {env : PEnv} {func : Func}
    {calleeId : ContextId} {context : Context} {impl : Impl} {syntaxArgs : List Arg}
    {args : List ValueId} {origin : OriginId} {index slot : Nat} {mutability : Mutability}
    {parameter : Param}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[calleeId]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    (environment : env.mod = module)
    (trace : CallArgumentsTrace env syntaxArgs args func calleeId origin)
    (parameterAt : impl.params[index]? = some parameter)
    (reference : ((lowerContextAt module context impl).params[index]?).any Ty.isRefSlice = true)
    (argumentAt : syntaxArgs[index]? = some (.byRef mutability (.var slot))) :
    ∃ localVar, env.impl.vars[slot]? = some localVar ∧ localVar.ty.isRefLike = true ∧
      localVar.ty.isRefSlice = false := by
  have aligned := ((validate_modOk module accepted).impl context.impl impl implAt |>.params
    index parameter parameterAt).1
  have nativeReference : (tyOfVar impl parameter.var).isRefSlice = true := by
    change ((impl.params.toList.map fun parameter => tyOfVar impl parameter.var)[index]?).any Ty.isRefSlice = true at reference
    simpa only [List.getElem?_map, Array.getElem?_toList, parameterAt,
      Option.map_some, Option.any_some] using reference
  cases variableAt : impl.vars[parameter.var]? with
  | none => simp [tyOfVar, variableAt, Ty.isRefSlice] at nativeReference
  | some parameterVar =>
    have sourceReference : parameterVar.ty.isRefSlice = true := by simpa [tyOfVar, variableAt] using nativeReference
    obtain ⟨actualParameter, actualAt, _, mode⟩ :=
      SummaryPreservation.accepted_refSlice_parameter accepted implAt variableAt sourceReference
    rw [aligned] at actualAt
    have sameParameter : actualParameter = parameter := Option.some.inj (actualAt.symm.trans parameterAt)
    subst actualParameter
    obtain ⟨returnTypes, initial, final, root, path, run, generated, live, continuation,
      location, valid, projects, typing, start, finish, type, moduleEq, variablesEq, source⟩ := trace
    obtain ⟨actualContext, actualImpl, argsStart, argsFinish, resultStart,
      actualContextAt, actualImplAt, arity, typedArgs, _⟩ := tyExpr_call_tables source
    rw [moduleEq, environment] at actualContextAt actualImplAt
    have sameContext : actualContext = context := Option.some.inj (actualContextAt.symm.trans contextAt)
    subst actualContext
    have sameImpl : actualImpl = impl := Option.some.inj (actualImplAt.symm.trans implAt)
    subst actualImpl
    obtain ⟨localVar, localAt, localReference, ordinary⟩ := tyArgs_refSlice_local_argument
      typedArgs arity (by simpa only [Array.getElem?_toList] using parameterAt)
      mode variableAt sourceReference argumentAt
    exact ⟨localVar, by simpa only [variablesEq] using localAt, localReference, ordinary⟩

#print axioms trace_refSlice_local_argument

end Goose.Lower.Validation.AdmittedSourceCalls
