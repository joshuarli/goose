import Goose.Proofs.ConstructionGhostCallArguments

namespace Goose.Proofs.ConstructionGhostValueCall
open Goose.Construct Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostArguments

def valueCallContinuation (origin : Goose.Core.OriginId) (result : ExecutionStep (List Carrier)) : ExecutionStep Value :=
  match result with
  | .ok carriers state => (do
      publishCarriers origin carriers
      carrierValue (← singleCarrier carriers)) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem evalValue_call_argumentReplay (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
    (before lookupReady callStart callLookupReady argumentsReady : ExecutionState)
    (id : Goose.Core.ImplId) (implementation : Impl) (channels callableChannels : List Channel)
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (preparedResults : channelsFor config.layout environment.act implementation.results.toList origin lookupReady = .ok channels callStart)
    (callLookup : getImplementation config context callStart = .ok (id, implementation) callLookupReady)
    (arity : channels.length = implementation.results.size)
    (preparedChannels : prepareCallableChannels environment channels implementation origin callLookupReady = .ok callableChannels argumentsReady) :
    ∃ outcome visits,
      ArgumentReplay config environment implementation.vars fuel 0 implementation.params.toList arguments argumentsReady outcome visits ∧
      visits.map ArgumentInvocation.argument = arguments.take visits.length ∧
      (visits.map ArgumentInvocation.ordinal).Nodup ∧
      evalValue (fuel + 2) config environment (.call context arguments origin) before =
        valueCallContinuation origin (callArgumentsContinuation fuel config id implementation channels callableChannels origin outcome) := by
  obtain ⟨outcome, visits, replay, ordered, once, execution⟩ :=
    invokeCall_argumentReplay fuel config environment context arguments channels origin callStart callLookupReady argumentsReady
      id implementation callableChannels callLookup arity preparedChannels
  refine ⟨outcome, visits, replay, ordered, once, ?_⟩
  simp only [evalValue, bind, lookup, preparedResults, execution, valueCallContinuation]
  cases callArgumentsContinuation fuel config id implementation channels callableChannels origin outcome <;> rfl

private def witnessModule : Module :=
  ⟨#[], #[], #[], #[⟨"callee", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
    #[⟨"x", .int .i64, .immutable, 0, 0⟩],
    .mk 0 [.print [.text "callee"] 0] (some (.lit .i64 8)), .unknown⟩],
    #[⟨0, "callee", [], [], []⟩], 0, #[], #[], #[]⟩
private def witnessExpression : Expr := .call 0
  [.byVal (.blockE (.mk 1 [.print [.text "arg"] 0] (some (.lit .i64 7))) 0)] 0
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem valueCallWitness :
    ∃ after, evalValue 60 ⟨.release, witnessModule⟩ ⟨0, 4, #[], [], []⟩ witnessExpression .initial =
      .ok (.int .i64 8) after ∧ after.construction.stdout.data.toList =
        [97, 114, 103, 10, 99, 97, 108, 108, 101, 101, 10] := by
  refine ⟨witnessState (evalValue 60 ⟨.release, witnessModule⟩ ⟨0, 4, #[], [], []⟩ witnessExpression .initial), ?_, ?_⟩ <;>
    unfold witnessState witnessExpression witnessModule <;> cbv

#print axioms valueCallWitness
#print axioms evalValue_call_argumentReplay
end Goose.Proofs.ConstructionGhostValueCall
