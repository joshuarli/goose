import Goose.Proofs.ExitExecutionPathCallUnwind
import Goose.Proofs.ExitExecutionPathArgumentUnwind
import Goose.Proofs.ExitExecutionPathCatch

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem moduleGlobals_escape_after_child (fuel : Nat) (config : EvalConfig)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (evaluated : initGlobals fuel config (List.range config.module.globals.size) initial = .escape address carriers final) :
    runModule fuel config initial = .escape address carriers final := by simp only [runModule, bind, evaluated]

#print axioms moduleGlobals_escape_after_child

theorem moduleEntry_escape_after_child (fuel : Nat) (config : EvalConfig)
    (initial globalsState implementationState entryState final : ExecutionState)
    (id : Goose.Core.ImplId) (implementation : Impl) (channels : List Channel) (address : ExitAddress) (carriers : List Carrier)
    (globals : initGlobals fuel config (List.range config.module.globals.size) initial = .ok () globalsState)
    (lookup : getImplementation config config.module.entry globalsState = .ok (id, implementation) implementationState)
    (receiving : channelsFor config.layout 0 implementation.results.toList 0 implementationState = .ok channels entryState)
    (evaluated : invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 entryState = .escape address carriers final) :
    runModule fuel config initial = .escape address carriers final := by simp only [runModule, bind, globals, lookup, receiving, evaluated]

#print axioms moduleEntry_escape_after_child

theorem activationScope_escape_after_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))  (body : Block)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (evaluated : (ExitInvocation.activationScope fuel environment pre body).action config initial = .escape address carriers final) :
    execActivationBody (fuel + 1) config environment pre body initial = .escape address carriers final := by
  simp only [ExitInvocation.action] at evaluated
  simp only [execActivationBody, bind, evaluated]

#print axioms activationScope_escape_after_child

theorem resultBlockWith_escape_after_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (body : Block)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (evaluated : execResultBlockWith fuel config environment [] channels body initial = .escape address carriers final) :
    execResultBlock (fuel + 1) config environment channels body initial = .escape address carriers final := by simpa only [execResultBlock] using evaluated

#print axioms resultBlockWith_escape_after_child

theorem resultScope_escape_after_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (evaluated : (ExitInvocation.resultScope fuel environment pre channels body).action config initial = .escape address carriers final) :
    execResultBlockWith (fuel + 1) config environment pre channels body initial = .escape address carriers final := by simpa only [execResultBlockWith, ExitInvocation.action] using evaluated

#print axioms resultScope_escape_after_child

theorem CallActivationPrefix.escape_call {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {context : Goose.Core.ContextId} {arguments : List Arg} {channels : List Channel} {origin : Goose.Core.OriginId}
    {initial entered final : ExecutionState} {activation : RuntimeActivation}
    {pre : List (Goose.Core.VarId × Value)} {body : Block} (address : ExitAddress) (carriers : List Carrier)
    (preparedCall : CallActivationPrefix fuel config environment context arguments channels origin initial activation pre body entered)
    (evaluated : enterActivation fuel config activation pre body origin entered = .escape address carriers final) :
    invokeCall (fuel + 1) config environment context arguments channels origin initial = .escape address carriers final := by
  rw [preparedCall.invokeCall_tail]
  simp only [bind, evaluated]

#print axioms CallActivationPrefix.escape_call

theorem ArgumentValuePrefix.escape_arguments {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {vars : Array LocalVar} {parameter : Param}
    {argument : Arg} {initial middle final : ExecutionState} {value : Value}
    (normal : ArgumentValuePrefix fuel config environment vars parameter argument initial value middle)
    (parameters : List Param) (arguments : List Arg) (address : ExitAddress) (carriers : List Carrier)
    (evaluated : evalArguments fuel config environment vars parameters arguments middle = .escape address carriers final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) (argument :: arguments) initial = .escape address carriers final := by
  rw [normal.evalArguments_tail parameters arguments]
  simp only [bind, evaluated]

#print axioms ArgumentValuePrefix.escape_arguments

theorem moduleGlobals_stop_after_child (fuel : Nat) (config : EvalConfig)
    (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (evaluated : initGlobals fuel config (List.range config.module.globals.size) initial = .stop reason final) :
    runModule fuel config initial = .stop reason final := by simp only [runModule, bind, evaluated]

#print axioms moduleGlobals_stop_after_child

theorem moduleEntry_stop_after_child (fuel : Nat) (config : EvalConfig)
    (initial globalsState implementationState entryState final : ExecutionState)
    (id : Goose.Core.ImplId) (implementation : Impl) (channels : List Channel) (reason : Goose.Core.Stop)
    (globals : initGlobals fuel config (List.range config.module.globals.size) initial = .ok () globalsState)
    (lookup : getImplementation config config.module.entry globalsState = .ok (id, implementation) implementationState)
    (receiving : channelsFor config.layout 0 implementation.results.toList 0 implementationState = .ok channels entryState)
    (evaluated : invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 entryState = .stop reason final) :
    runModule fuel config initial = .stop reason final := by simp only [runModule, bind, globals, lookup, receiving, evaluated]

#print axioms moduleEntry_stop_after_child

theorem activationScope_stop_after_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))  (body : Block)
    (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (evaluated : (ExitInvocation.activationScope fuel environment pre body).action config initial = .stop reason final) :
    execActivationBody (fuel + 1) config environment pre body initial = .stop reason final := by
  simp only [ExitInvocation.action] at evaluated
  simp only [execActivationBody, bind, evaluated]

#print axioms activationScope_stop_after_child

theorem resultBlockWith_stop_after_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (body : Block)
    (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (evaluated : execResultBlockWith fuel config environment [] channels body initial = .stop reason final) :
    execResultBlock (fuel + 1) config environment channels body initial = .stop reason final := by simpa only [execResultBlock] using evaluated

#print axioms resultBlockWith_stop_after_child

theorem resultScope_stop_after_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block)
    (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (evaluated : (ExitInvocation.resultScope fuel environment pre channels body).action config initial = .stop reason final) :
    execResultBlockWith (fuel + 1) config environment pre channels body initial = .stop reason final := by simpa only [execResultBlockWith, ExitInvocation.action] using evaluated

#print axioms resultScope_stop_after_child

theorem CallActivationPrefix.stop_call {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {context : Goose.Core.ContextId} {arguments : List Arg} {channels : List Channel} {origin : Goose.Core.OriginId}
    {initial entered final : ExecutionState} {activation : RuntimeActivation}
    {pre : List (Goose.Core.VarId × Value)} {body : Block} (reason : Goose.Core.Stop)
    (preparedCall : CallActivationPrefix fuel config environment context arguments channels origin initial activation pre body entered)
    (evaluated : enterActivation fuel config activation pre body origin entered = .stop reason final) :
    invokeCall (fuel + 1) config environment context arguments channels origin initial = .stop reason final := by
  rw [preparedCall.invokeCall_tail]
  simp only [bind, evaluated]

#print axioms CallActivationPrefix.stop_call

theorem ArgumentValuePrefix.stop_arguments {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {vars : Array LocalVar} {parameter : Param}
    {argument : Arg} {initial middle final : ExecutionState} {value : Value}
    (normal : ArgumentValuePrefix fuel config environment vars parameter argument initial value middle)
    (parameters : List Param) (arguments : List Arg) (reason : Goose.Core.Stop)
    (evaluated : evalArguments fuel config environment vars parameters arguments middle = .stop reason final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) (argument :: arguments) initial = .stop reason final := by
  rw [normal.evalArguments_tail parameters arguments]
  simp only [bind, evaluated]

#print axioms ArgumentValuePrefix.stop_arguments

theorem enterActivation_stop_after_body (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (origin : Goose.Core.OriginId) (implementation : Impl) (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (lookup : config.module.impls[activation.implementation]? = some implementation)
    (stopped : execActivationBody fuel config activation pre body initial = .stop reason final) :
    enterActivation (fuel + 1) config activation pre body origin initial = .stop reason final := by
  simp only [enterActivation, lookup, finishActivation, stopped]

#print axioms enterActivation_stop_after_body

end Goose.Proofs.ExitExecution
