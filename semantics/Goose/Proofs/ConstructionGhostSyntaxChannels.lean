import Goose.Proofs.ConstructionGhostSyntaxFuel
import Goose.Proofs.ConstructionGhostCallActivation

namespace Goose.Proofs.ConstructionGhostSyntaxChannels
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostCallArguments
open Goose.Proofs.ConstructionGhostCallActivation Goose.Proofs.ConstructionGhostArguments

theorem channelCall_argumentHistory (fuel : Nat) (config : EvalConfig) (closed : ClosedModule config)
    (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (arguments : List Arg)
    (channels : List Channel) (origin : Goose.Core.OriginId) (path : List Nat)
    (before lookupReady argumentsReady : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl)
    (callableChannels : List Channel)
    (lookup : getImplementation config contextId before = .ok (id, implementation) lookupReady)
    (arity : channels.length = implementation.results.size)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady)
    (derivation : ArgumentSyntax config implementation.params.toList arguments) :
    ∃ outcome visits,
      ArgumentReplay config environment implementation.vars fuel 0 implementation.params.toList arguments argumentsReady outcome visits ∧
      visits.map ArgumentInvocation.argument = arguments.take visits.length ∧
      (visits.map ArgumentInvocation.ordinal).Nodup ∧
      invokeCall (fuel + 1) config environment contextId arguments channels origin before =
        callArgumentsContinuation fuel config id implementation channels callableChannels origin outcome ∧
      SourceHistory config fuel path (.arguments environment implementation.vars implementation.params.toList arguments)
        argumentsReady (evalArguments fuel config environment implementation.vars implementation.params.toList arguments argumentsReady) := by
  obtain ⟨outcome, visits, replay, ordered, once, execution⟩ :=
    invokeCall_argumentReplay fuel config environment contextId arguments channels origin before lookupReady argumentsReady
      id implementation callableChannels lookup arity prepared
  exact ⟨outcome, visits, replay, ordered, once, execution,
    fuelHistory_exists fuel config _ path argumentsReady
      ((syntaxFuel_exists fuel config closed).arguments environment implementation.vars implementation.params.toList arguments derivation)⟩

theorem channelCall_activationHistory (fuel : Nat) (config : EvalConfig) (closed : ClosedModule config)
    (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (arguments : List Arg)
    (channels : List Channel) (origin : Goose.Core.OriginId) (path : List Nat)
    (before lookupReady argumentsReady valuesReady activationReady : ExecutionState)
    (context : Context) (implementation : Impl) (callableChannels refreshed : List Channel) (values : List Value)
    (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (lookup : getImplementation config contextId before = .ok (context.impl, implementation) lookupReady)
    (arity : channels.length = implementation.results.size)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady)
    (argumentsResult : evalArguments fuel config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady)
    (refresh : refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady)
    (depth : activationReady.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨context.impl, activationReady.nextAct, implementation.vars, [], refreshed⟩
    let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
    let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
    invokeCall (fuel + 1) config environment contextId arguments channels origin before =
      (enterActivation fuel config activation pre implementation.body origin >>= fun carriers =>
        deliverCarriers fuel config.layout channels carriers origin) activated ∧
    SourceHistory config fuel path (.boundActivation activation pre implementation.body origin) activated
      (enterActivation fuel config activation pre implementation.body origin activated) := by
  dsimp only
  obtain ⟨outcome, visits, replay, ordered, once, execution⟩ :=
    invokeCall_argumentReplay fuel config environment contextId arguments channels origin before lookupReady argumentsReady
      context.impl implementation callableChannels lookup arity prepared
  have actual := replay.sound
  rw [argumentsResult] at actual
  subst outcome
  constructor
  · rw [execution]
    exact callAfterArguments_activation fuel config context.impl implementation channels callableChannels refreshed origin values
      valuesReady activationReady refresh depth
  · obtain ⟨scope, statements, body, derivation⟩ := closed contextId context implementation contextFound implementationFound
    rw [body]
    exact fuelHistory_exists fuel config _ path _
      ((syntaxFuel_exists fuel config closed).activation _ _ scope statements origin derivation)

#print axioms channelCall_argumentHistory
#print axioms channelCall_activationHistory
end Goose.Proofs.ConstructionGhostSyntaxChannels
