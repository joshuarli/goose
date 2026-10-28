import Goose.Proofs.ConstructionAcceptedRegisterCallExecution

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem invokeCall_singleArgument_register_stopped (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (target : Nat) (context : Context) (implementation : Impl) (parameter : Param) (argument : Arg)
    (ty : Ty) (origin : Nat) (state after : ExecutionState) (reason : Goose.Core.Stop)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (stopped : evalArguments fuel config environment implementation.vars [parameter] [argument] state = .stop reason after) :
    invokeCall (fuel + 1) config environment target [argument] [.register ty] origin state = .stop reason after := by
  simp [invokeCall, getImplementation, contextAt, implementationAt, parameters, results, stopped, bind, pure]

theorem invokeCall_singleArgument_register_transition (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (target : Nat) (context : Context) (implementation : Impl) (parameter : Param) (argument : Arg)
    (ty : Ty) (origin : Nat) (state argumentState : ExecutionState) (value : Value)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (evaluated : evalArguments (fuel + 1) config environment implementation.vars [parameter] [argument] state =
      .ok [value] argumentState) :
    let activation : RuntimeActivation := ⟨context.impl, argumentState.nextAct, implementation.vars, [], [.register ty]⟩
    let pushed := { argumentState with nextAct := argumentState.nextAct + 1, activations := activation :: argumentState.activations }
    invokeCall (fuel + 2) config environment target [argument] [.register ty] origin state =
      if argumentState.activations.length ≥ Goose.Core.maxCallDepth then .stop .timeout argumentState
      else (do let carriers ← enterActivation (fuel + 1) config activation [(parameter.var, value)] implementation.body origin
               deliverCarriers (fuel + 1) config.layout [.register ty] carriers origin) pushed := by
  by_cases depth : argumentState.activations.length ≥ Goose.Core.maxCallDepth
  · simp [invokeCall, getImplementation, contextAt, implementationAt, parameters, results, evaluated,
      depth, timeout, EvalM.stop, EvalM.get, EvalM.set, bind, pure]
  · simp [invokeCall, getImplementation, contextAt, implementationAt, parameters, results, evaluated,
      depth, freshAct, EvalM.get, EvalM.set, bind, pure]

#print axioms invokeCall_singleArgument_register_transition
#print axioms invokeCall_singleArgument_register_stopped
end Goose.Proofs.ConstructionAcceptedExecution
