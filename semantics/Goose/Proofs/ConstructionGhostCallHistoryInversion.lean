import Goose.Proofs.ConstructionGhostDeclarationNestedCall

namespace Goose.Proofs.ConstructionGhostCallHistoryInversion
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation

def channelCallSyntax : SourceOperation α → Option (RuntimeActivation × Goose.Core.ContextId × List Arg × List Channel × Goose.Core.OriginId)
  | .channelCall environment context arguments channels origin => some (environment, context, arguments, channels, origin)
  | _ => none

theorem call_activation_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (environment : RuntimeActivation) (context : Goose.Core.ContextId)
    (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (lookupReady argumentsReady valuesReady activationReady : ExecutionState)
    (id : Goose.Core.ImplId) (implementation : Impl) (callableChannels refreshed : List Channel) (values : List Value)
    (fuelEq : fuel = sourceFuel + 1)
    (operationEq : channelCallSyntax operation = some (environment, context, arguments, channels, origin))
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (arity : channels.length = implementation.results.size)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady)
    (argumentsResult : evalArguments sourceFuel config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady)
    (refresh : refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady)
    (depth : activationReady.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩
    let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
    let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
    SourceHistory config sourceFuel (path ++ [1]) (.boundActivation activation pre implementation.body origin) activated
      (enterActivation sourceFuel config activation pre implementation.body origin activated) := by
  cases history <;> simp_all [channelCallSyntax]
  case channelCall =>
    rename_i activationChildren
    exact activationChildren id implementation lookupReady callableChannels argumentsReady values valuesReady refreshed activationReady
      rfl rfl rfl prepared argumentsResult refresh depth

#print axioms call_activation_history
end Goose.Proofs.ConstructionGhostCallHistoryInversion
