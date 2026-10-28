import Goose.Proofs.ConstructionGhostSyntaxFuel
import Goose.Proofs.ConstructionGhostCallActivation

namespace Goose.Proofs.ConstructionGhostSyntaxChannels
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostCallArguments
open Goose.Proofs.ConstructionGhostCallActivation Goose.Proofs.ConstructionGhostArguments

theorem channelCall_history (fuel : Nat) (config : EvalConfig) (closed : ClosedModule config)
    (environment : RuntimeActivation) (context : Goose.Core.ContextId) (arguments : List Arg)
    (channels : List Channel) (origin : Goose.Core.OriginId) (path : List Nat) (before : ExecutionState)
    (argumentSyntax : ∀ id implementation start lookupReady,
      getImplementation config context start = .ok (id, implementation) lookupReady →
      ArgumentSyntax config implementation.params.toList arguments) :
    SourceHistory config fuel path (.channelCall environment context arguments channels origin) before
      (invokeCall fuel config environment context arguments channels origin before) := by
  exact fuelHistory_exists fuel config _ path before
    ((syntaxFuel_exists fuel config closed).channelCall environment context arguments channels origin argumentSyntax)

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

private def witnessContext : Context := ⟨0, "channel", [], [], []⟩
private def witnessImplementation : Impl := ⟨"channel", #[], #[⟨.unit, .register, none⟩], #[],
  .mk 0 [.print [.text "x"] 0] none, .unknown⟩
private def witnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[witnessImplementation], #[witnessContext], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem witnessClosed : ClosedModule witnessConfig := by
  intro contextId context implementation contextFound implementationFound
  cases contextId with
  | zero =>
      have contextEq : context = witnessContext := by simpa [witnessConfig] using contextFound.symm
      subst context
      have implEq : implementation = witnessImplementation := by
        simpa [witnessConfig, witnessContext] using implementationFound.symm
      subst implementation
      refine ⟨0, [.print [.text "x"] 0], rfl, ?_⟩
      intro statement member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst statement
      exact .printText "x" 0
  | succ contextId => simp [witnessConfig] at contextFound

private theorem witnessArguments : ∀ id implementation start ready,
    getImplementation witnessConfig 0 start = .ok (id, implementation) ready →
    ArgumentSyntax witnessConfig implementation.params.toList [] := by
  intro id implementation start ready lookup
  obtain ⟨context, found, idEqual, implFound⟩ := implementation_lookup_source witnessConfig 0 start ready id implementation lookup
  have contextEq : context = witnessContext := by simpa [witnessConfig] using found.symm
  subst context
  subst id
  have implEq : implementation = witnessImplementation := by
    simpa [witnessConfig, witnessContext] using implFound.symm
  subst implementation
  exact .nil

theorem witness_registerChannel : ∃ after,
    invokeCall 30 witnessConfig witnessEnvironment 0 [] [.register .unit] 0 .initial = .ok [.register .unit] after ∧
    after.construction.stdout.data.toList = [120, 10] ∧
    SourceHistory witnessConfig 30 [] (.channelCall witnessEnvironment 0 [] [.register .unit] 0) .initial (.ok [.register .unit] after) := by
  have history := channelCall_history 30 witnessConfig witnessClosed witnessEnvironment 0 [] [.register .unit] 0 [] .initial witnessArguments
  refine ⟨witnessState (invokeCall 30 witnessConfig witnessEnvironment 0 [] [.register .unit] 0 .initial), ?_, ?_, ?_⟩
  · unfold witnessState witnessConfig witnessContext witnessImplementation witnessEnvironment
    cbv
  · unfold witnessState witnessConfig witnessContext witnessImplementation witnessEnvironment
    cbv
  · have actual : invokeCall 30 witnessConfig witnessEnvironment 0 [] [.register .unit] 0 .initial =
        .ok [.register .unit] (witnessState (invokeCall 30 witnessConfig witnessEnvironment 0 [] [.register .unit] 0 .initial)) := by
      unfold witnessState witnessConfig witnessContext witnessImplementation witnessEnvironment
      cbv
    rw [actual] at history
    exact history

#print axioms witness_registerChannel
#print axioms channelCall_history
#print axioms channelCall_argumentHistory
#print axioms channelCall_activationHistory
end Goose.Proofs.ConstructionGhostSyntaxChannels
