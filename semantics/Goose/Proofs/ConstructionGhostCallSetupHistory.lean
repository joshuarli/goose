import Goose.Proofs.ConstructionGhostCallSetup
import Goose.Proofs.ConstructionGhostCallHistoryInversion

namespace Goose.Proofs.ConstructionGhostCallSetupHistory
open Goose.Construct Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostArguments
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostCallHistoryInversion
open Goose.Proofs.ConstructionGhostCallSetup Goose.Proofs.ConstructionGhostSourceFuel Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionGhostSyntaxFuel

theorem call_arguments_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (environment : RuntimeActivation) (context : Goose.Core.ContextId)
    (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (lookupReady argumentsReady : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl)
    (callableChannels : List Channel)
    (fuelEq : fuel = sourceFuel + 1)
    (operationEq : channelCallSyntax operation = some (environment, context, arguments, channels, origin))
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (arity : channels.length = implementation.results.size)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady) :
    SourceHistory config sourceFuel (path ++ [0]) (.arguments environment implementation.vars implementation.params.toList arguments) argumentsReady
      (evalArguments sourceFuel config environment implementation.vars implementation.params.toList arguments argumentsReady) := by
  cases history <;> simp_all [channelCallSyntax]

def CallSetupHistory (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) (before : ExecutionState) : Prop :=
    (∃ terminal, terminalCall (getImplementation config context before) = some terminal ∧
      invokeCall (fuel + 1) config environment context arguments channels origin before = terminal) ∨
    (∃ id implementation lookupReady, getImplementation config context before = .ok (id, implementation) lookupReady ∧
      channels.length ≠ implementation.results.size ∧
      invokeCall (fuel + 1) config environment context arguments channels origin before = .stop (.fault .arity) lookupReady) ∨
    (∃ id implementation lookupReady terminal, getImplementation config context before = .ok (id, implementation) lookupReady ∧
      channels.length = implementation.results.size ∧
      terminalCall (prepareCallableChannels environment channels implementation origin lookupReady) = some terminal ∧
      invokeCall (fuel + 1) config environment context arguments channels origin before = terminal) ∨
    (∃ id implementation lookupReady callableChannels argumentsReady outcome visits,
      getImplementation config context before = .ok (id, implementation) lookupReady ∧
      channels.length = implementation.results.size ∧
      prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady ∧
      ArgumentReplay config environment implementation.vars fuel 0 implementation.params.toList arguments argumentsReady outcome visits ∧
      SourceHistory config fuel (path ++ [0]) (.arguments environment implementation.vars implementation.params.toList arguments) argumentsReady outcome ∧
      invokeCall (fuel + 1) config environment context arguments channels origin before =
        callArgumentsContinuation fuel config id implementation channels callableChannels origin outcome)

theorem invokeCall_setupHistory (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) (before : ExecutionState)
    (history : SourceHistory config (fuel + 1) path (.channelCall environment context arguments channels origin) before
      (invokeCall (fuel + 1) config environment context arguments channels origin before)) : CallSetupHistory fuel config environment path context arguments channels origin before := by
  unfold CallSetupHistory
  rcases invokeCall_setupClassification fuel config environment context arguments channels origin before with
    lookupTerminal | arityFault | preparationTerminal | ⟨id, implementation, lookupReady, callableChannels, argumentsReady,
      outcome, visits, lookup, arity, prepared, replay, execution⟩
  · exact Or.inl lookupTerminal
  · exact Or.inr (Or.inl arityFault)
  · exact Or.inr (Or.inr (Or.inl preparationTerminal))
  · have argumentsHistory := call_arguments_history history fuel environment context arguments channels origin lookupReady argumentsReady
      id implementation callableChannels rfl rfl lookup arity prepared
    rw [replay.sound] at argumentsHistory
    exact Or.inr (Or.inr (Or.inr ⟨id, implementation, lookupReady, callableChannels, argumentsReady, outcome, visits,
      lookup, arity, prepared, replay, argumentsHistory, execution⟩))

theorem invokeCall_validatedSetupHistory (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) (before : ExecutionState) (closed : ClosedModuleWithTails config)
    (argumentsSyntax : ∀ id implementation start lookupReady,
      getImplementation config context start = .ok (id, implementation) lookupReady →
      ArgumentSyntax config implementation.params.toList arguments) :
    CallSetupHistory fuel config environment path context arguments channels origin before := by
  have support := (syntaxFuel_existsWithTails (fuel + 1) config closed).channelCall environment context arguments channels origin argumentsSyntax
  have history := fuelHistory_exists (fuel + 1) config (.channelCall environment context arguments channels origin) path before support
  exact invokeCall_setupHistory fuel config environment path context arguments channels origin before history

theorem invokeCall_validatedActivationHistory (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) (before : ExecutionState) (closed : ClosedModuleWithTails config)
    (argumentsSyntax : ∀ id implementation start lookupReady,
      getImplementation config context start = .ok (id, implementation) lookupReady →
      ArgumentSyntax config implementation.params.toList arguments) :
    CallSetupHistory fuel config environment path context arguments channels origin before ∧
    ∀ id implementation lookupReady callableChannels argumentsReady values valuesReady refreshed activationReady,
      getImplementation config context before = .ok (id, implementation) lookupReady →
      channels.length = implementation.results.size →
      prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady →
      evalArguments fuel config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady →
      refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady →
      activationReady.activations.length < Goose.Core.maxCallDepth →
      let activation : RuntimeActivation := ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩
      let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
      let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
      SourceHistory config fuel (path ++ [1]) (.boundActivation activation pre implementation.body origin) activated
        (enterActivation fuel config activation pre implementation.body origin activated) := by
  have support := (syntaxFuel_existsWithTails (fuel + 1) config closed).channelCall environment context arguments channels origin argumentsSyntax
  have history := fuelHistory_exists (fuel + 1) config (.channelCall environment context arguments channels origin) path before support
  refine ⟨invokeCall_setupHistory fuel config environment path context arguments channels origin before history, ?_⟩
  intro id implementation lookupReady callableChannels argumentsReady values valuesReady refreshed activationReady lookup arity prepared argumentResult refresh depth
  exact call_activation_history history fuel environment context arguments channels origin lookupReady argumentsReady valuesReady activationReady
    id implementation callableChannels refreshed values rfl rfl lookup arity prepared argumentResult refresh depth

#print axioms invokeCall_validatedActivationHistory
#print axioms invokeCall_validatedSetupHistory
#print axioms invokeCall_setupHistory
#print axioms call_arguments_history
end Goose.Proofs.ConstructionGhostCallSetupHistory
