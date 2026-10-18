import Goose.Proofs.ExitExecutionPathCalls

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem CallArgumentPrefix.escape_call {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {context : Goose.Core.ContextId} {arguments : List Arg} {channels : List Channel} {origin : Goose.Core.OriginId}
    {initial prepared final : ExecutionState} {id : Goose.Core.ImplId} {implementation : Impl}
    {firstChannels : List Channel} {address : ExitAddress} {carriers : List Carrier}
    (preparedCall : CallArgumentPrefix config context channels origin initial id implementation firstChannels prepared)
    (escaped : evalArguments fuel config environment implementation.vars implementation.params.toList arguments prepared =
      .escape address carriers final) :
    invokeCall (fuel + 1) config environment context arguments channels origin initial = .escape address carriers final := by
  cases preparedCall with
  | actual lookupState firstState id implementation firstChannels lookup arity receiving =>
      simp only [invokeCall, bind, lookup, arity, Bool.false_eq_true, ↓reduceIte]
      erw [receiving]
      simp only [escaped]

theorem CallArgumentPrefix.stop_call {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {context : Goose.Core.ContextId} {arguments : List Arg} {channels : List Channel} {origin : Goose.Core.OriginId}
    {initial prepared final : ExecutionState} {id : Goose.Core.ImplId} {implementation : Impl}
    {firstChannels : List Channel} {reason : Goose.Core.Stop}
    (preparedCall : CallArgumentPrefix config context channels origin initial id implementation firstChannels prepared)
    (stopped : evalArguments fuel config environment implementation.vars implementation.params.toList arguments prepared =
      .stop reason final) :
    invokeCall (fuel + 1) config environment context arguments channels origin initial = .stop reason final := by
  cases preparedCall with
  | actual lookupState firstState id implementation firstChannels lookup arity receiving =>
      simp only [invokeCall, bind, lookup, arity, Bool.false_eq_true, ↓reduceIte]
      erw [receiving]
      simp only [stopped]

theorem CallActivationPrefix.invokeCall_tail {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {context : Goose.Core.ContextId} {arguments : List Arg} {channels : List Channel} {origin : Goose.Core.OriginId}
    {initial entered : ExecutionState} {activation : RuntimeActivation}
    {pre : List (Goose.Core.VarId × Value)} {body : Block}
    (preparedCall : CallActivationPrefix fuel config environment context arguments channels origin initial activation pre body entered) :
    invokeCall (fuel + 1) config environment context arguments channels origin initial =
      (enterActivation fuel config activation pre body origin >>= fun carriers =>
        deliverCarriers fuel config.layout channels carriers origin) entered := by
  cases preparedCall with
  | actual firstState argumentState ready id implementation firstChannels renewed values receiving argumentsDone renewal depth =>
      cases receiving with
      | actual lookupState firstState id implementation firstChannels lookup arity receiving =>
          simp only [invokeCall, bind, lookup, arity, Bool.false_eq_true, ↓reduceIte]
          erw [receiving]
          simp only [argumentsDone]
          erw [renewal]
          simp only [EvalM.get, bind, Nat.not_le_of_gt depth, ↓reduceIte, freshAct, EvalM.set, pure]

#print axioms CallArgumentPrefix.escape_call
#print axioms CallArgumentPrefix.stop_call
#print axioms CallActivationPrefix.invokeCall_tail

end Goose.Proofs.ExitExecution
