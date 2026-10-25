import Goose.Lower.Validation.AdmittedSourceCallTraceTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

private theorem native_args_length (arguments : List Arg) (env : LEnv) (initial : LS) :
    (lowerArgs arguments env initial).1.length = arguments.length := by
  induction arguments generalizing initial with
  | nil => rfl
  | cons first rest ih =>
    simpa only [lowerArgs, bind_run, pure_run, List.length_cons] using
      congrArg Nat.succ (ih (lowerArg first env initial).2)

theorem CallArgumentsTrace.arity {module : Core.Module} {contextId : ContextId}
    {context : Context} {impl : Impl} {env : PEnv} {func : Func}
    {syntaxArgs : List Arg} {arguments : List ValueId} {origin : OriginId}
    (trace : CallArgumentsTrace env syntaxArgs arguments func contextId origin)
    (environment : env.mod = module)
    (contextAt : module.contexts[contextId]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    arguments.length = impl.params.size := by
  obtain ⟨returnTypes, initial, final, root, path, run, generated, live, continuation,
    location, valid, projects, typing, start, finish, type, moduleEq, variablesEq, source⟩ := trace
  obtain ⟨actualContext, actualImpl, argsStart, argsFinish, resultStart,
    actualContextAt, actualImplAt, arity, typedArgs, _⟩ := tyExpr_call_tables source
  rw [moduleEq, environment] at actualContextAt actualImplAt
  have sameContext : actualContext = context := Option.some.inj (actualContextAt.symm.trans contextAt)
  subst actualContext
  have sameImpl : actualImpl = impl := Option.some.inj (actualImplAt.symm.trans implAt)
  subst actualImpl
  have nativeLength := native_args_length syntaxArgs (lowerEnv env.mod env.impl.vars returnTypes) initial
  rw [run] at nativeLength
  exact nativeLength.trans (by simpa only [Array.length_toList] using arity.symm)

#print axioms CallArgumentsTrace.arity

end Goose.Lower.Validation.ReplacementContentFlowSource
