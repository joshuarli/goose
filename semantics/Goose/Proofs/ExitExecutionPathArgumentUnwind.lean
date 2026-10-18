import Goose.Proofs.ExitExecutionPathArguments

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem ArgumentValuePrefix.evalArguments_tail {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {vars : Array LocalVar} {parameter : Param}
    {argument : Arg} {initial middle : ExecutionState} {value : Value}
    (normal : ArgumentValuePrefix fuel config environment vars parameter argument initial value middle)
    (parameters : List Param) (arguments : List Arg) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) (argument :: arguments) initial =
      ((do pure (value :: (← evalArguments fuel config environment vars parameters arguments))) : EvalM (List Value)) middle := by
  cases normal
  all_goals simp_all only [evalArguments, bind, pure]

theorem argumentReference_escape_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (mutability : Goose.Core.Mutability) (place : Place) (arguments : List Arg) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (evaluated : evalPlace fuel config environment place initial = .escape address carriers final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) ((.byRef mutability place) :: arguments) initial =
      .escape address carriers final := by
  simp only [evalArguments, bind, evaluated]

#print axioms argumentReference_escape_after_child

theorem argumentValue_escape_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (operand : Expr) (arguments : List Arg) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (evaluated : evalValue fuel config environment operand initial = .escape address carriers final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) ((.byVal operand) :: arguments) initial =
      .escape address carriers final := by
  simp only [evalArguments, bind, evaluated]

#print axioms argumentValue_escape_after_child

theorem argumentMaterialize_escape_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (operand : Expr) (descriptor : LocalVar) (count : Nat) (arguments : List Arg) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (lookup : vars[parameter.var]? = some descriptor)
    (materialized : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = some count)
    (evaluated : evalValue fuel config environment operand initial = .escape address carriers final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) ((.construct operand) :: arguments) initial =
      .escape address carriers final := by
  simp only [evalArguments, bind, lookup, materializeProducer, materialized, evaluated]

#print axioms argumentMaterialize_escape_after_child

theorem argumentBuild_escape_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (operand : Expr) (descriptor : LocalVar) (destination : Nat) (prepared : ExecutionState) (arguments : List Arg) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (lookup : vars[parameter.var]? = some descriptor)
    (materialized : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = none)
    (allocated : newDestination config.layout environment.act descriptor.ty .value (expressionOrigin operand) none
      (producerCount? ⟨config.module, environment.vars⟩ operand) initial = .ok destination prepared)
    (evaluated : buildExpr fuel config environment destination operand prepared = .escape address carriers final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) ((.construct operand) :: arguments) initial =
      .escape address carriers final := by
  simp only [EvalConfig.layout] at allocated
  simp only [evalArguments, bind, pure, lookup, materializeProducer, materialized, constructLocal, allocated, evaluated]

#print axioms argumentBuild_escape_after_child

theorem argumentReference_stop_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (mutability : Goose.Core.Mutability) (place : Place) (arguments : List Arg) (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (evaluated : evalPlace fuel config environment place initial = .stop reason final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) ((.byRef mutability place) :: arguments) initial =
      .stop reason final := by
  simp only [evalArguments, bind, evaluated]

#print axioms argumentReference_stop_after_child

theorem argumentValue_stop_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (operand : Expr) (arguments : List Arg) (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (evaluated : evalValue fuel config environment operand initial = .stop reason final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) ((.byVal operand) :: arguments) initial =
      .stop reason final := by
  simp only [evalArguments, bind, evaluated]

#print axioms argumentValue_stop_after_child

theorem argumentMaterialize_stop_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (operand : Expr) (descriptor : LocalVar) (count : Nat) (arguments : List Arg) (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (lookup : vars[parameter.var]? = some descriptor)
    (materialized : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = some count)
    (evaluated : evalValue fuel config environment operand initial = .stop reason final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) ((.construct operand) :: arguments) initial =
      .stop reason final := by
  simp only [evalArguments, bind, lookup, materializeProducer, materialized, evaluated]

#print axioms argumentMaterialize_stop_after_child

theorem argumentBuild_stop_after_child (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (operand : Expr) (descriptor : LocalVar) (destination : Nat) (prepared : ExecutionState) (arguments : List Arg) (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (lookup : vars[parameter.var]? = some descriptor)
    (materialized : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = none)
    (allocated : newDestination config.layout environment.act descriptor.ty .value (expressionOrigin operand) none
      (producerCount? ⟨config.module, environment.vars⟩ operand) initial = .ok destination prepared)
    (evaluated : buildExpr fuel config environment destination operand prepared = .stop reason final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) ((.construct operand) :: arguments) initial =
      .stop reason final := by
  simp only [EvalConfig.layout] at allocated
  simp only [evalArguments, bind, pure, lookup, materializeProducer, materialized, constructLocal, allocated, evaluated]

#print axioms argumentBuild_stop_after_child

#print axioms ArgumentValuePrefix.evalArguments_tail

end Goose.Proofs.ExitExecution
