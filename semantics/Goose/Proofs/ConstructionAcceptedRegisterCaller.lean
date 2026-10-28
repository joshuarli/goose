import Goose.Proofs.ConstructionAcceptedScalarResultProduce

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem evalValue_call_register (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId origin : Nat) (context : Context) (helper : Impl) (ty : Ty) (arguments : List Arg) (state : ExecutionState)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (results : helper.results = #[⟨ty, .register, none⟩]) :
    evalValue (fuel + 1) config environment (.call contextId arguments origin) state =
      (do let carriers ← invokeCall fuel config environment contextId arguments [.register ty] origin
          publishCarriers origin carriers
          carrierValue (← singleCarrier carriers)) state := by
  simp [evalValue, getImplementation, contextAt, helperAt, results, channelsFor, bind, pure]

theorem evalValue_call_register_success (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId origin : Nat) (context : Context) (helper : Impl) (ty : Ty) (arguments : List Arg)
    (state after : ExecutionState) (value : Value)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (results : helper.results = #[⟨ty, .register, none⟩])
    (returned : invokeCall fuel config environment contextId arguments [.register ty] origin state = .ok [.register value] after) :
    evalValue (fuel + 1) config environment (.call contextId arguments origin) state = .ok value after := by
  rw [evalValue_call_register fuel config environment contextId origin context helper ty arguments state contextAt helperAt results]
  simp [returned, bind, pure, publishCarriers, singleCarrier, carrierValue, liftConstruction,
    publishOperation, preflightPublication, ConstructionM.get, Except.pure, Except.bind]

theorem evalValue_call_register_outcomes (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId origin : Nat) (context : Context) (helper : Impl) (ty : Ty) (arguments : List Arg) (state : ExecutionState)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (results : helper.results = #[⟨ty, .register, none⟩])
    (shape : match invokeCall fuel config environment contextId arguments [.register ty] origin state with
      | .ok carriers _ => ∃ value, carriers = [.register value]
      | .stop .. => True | _ => False) :
    evalValue (fuel + 1) config environment (.call contextId arguments origin) state =
      match invokeCall fuel config environment contextId arguments [.register ty] origin state with
      | .ok [.register value] after => .ok value after
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers after
      | .jump target kind after => .jump target kind after
      | .ok _ after => .stop (.fault .shape) after := by
  cases invoked : invokeCall fuel config environment contextId arguments [.register ty] origin state with
  | escape target carriers after | jump target kind after => simp only [invoked] at shape
  | stop reason after =>
    rw [evalValue_call_register fuel config environment contextId origin context helper ty arguments state contextAt helperAt results]
    simp [invoked, bind]
  | ok carriers after =>
    simp only [invoked] at shape
    obtain ⟨value, rfl⟩ := shape
    exact evalValue_call_register_success fuel config environment contextId origin context helper ty arguments state after value
      contextAt helperAt results invoked

#print axioms evalValue_call_register_outcomes
#print axioms evalValue_call_register
#print axioms evalValue_call_register_success
end Goose.Proofs.ConstructionAcceptedExecution
