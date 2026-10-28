import Goose.Proofs.ConstructionGhostCallArguments

namespace Goose.Proofs.ConstructionGhostChannelTransition
open Goose.Construct Goose.Proofs.ConstructionGhostCallArguments

def channelPreparationResult (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Goose.Core.ImplId) (implementation : Impl) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) : ExecutionStep (List Channel) → ExecutionStep (List Carrier)
  | .ok callableChannels ready => callArgumentsContinuation fuel config id implementation channels callableChannels origin
      (evalArguments fuel config environment implementation.vars implementation.params.toList arguments ready)
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem invokeCall_preparation (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before lookupReady : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl)
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (arity : channels.length = implementation.results.size) :
    invokeCall (fuel + 1) config environment context arguments channels origin before =
      channelPreparationResult fuel config environment id implementation arguments channels origin
        (prepareCallableChannels environment channels implementation origin lookupReady) := by
  simp only [invokeCall, bind, lookup, arity, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  change (prepareCallableChannels environment channels implementation origin >>= fun selected =>
    evalArguments fuel config environment implementation.vars implementation.params.toList arguments >>= fun values =>
      callAfterArguments fuel config id implementation channels selected origin values) lookupReady = _
  cases prepared : prepareCallableChannels environment channels implementation origin lookupReady with
  | ok selected ready =>
      simp only [bind, prepared, channelPreparationResult, callArgumentsContinuation, callAfterArguments]
      cases evalArguments fuel config environment implementation.vars implementation.params.toList arguments ready <;> rfl
  | stop | escape | jump => simp_all only [bind, channelPreparationResult]

theorem invokeCall_badArity (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before lookupReady : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl)
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (arity : channels.length ≠ implementation.results.size) :
    invokeCall (fuel + 1) config environment context arguments channels origin before = .stop (.fault .arity) lookupReady := by
  simp [invokeCall, bind, lookup, arity, fault, EvalM.stop]

#print axioms invokeCall_preparation
#print axioms invokeCall_badArity
end Goose.Proofs.ConstructionGhostChannelTransition
