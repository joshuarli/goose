import Goose.Proofs.ConstructionGhostCallHistoryInversion

namespace Goose.Proofs.ConstructionGhostValueCallHistory
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual

def valueCallSyntax : SourceOperation α → Option (RuntimeActivation × Goose.Core.ContextId × List Arg × Goose.Core.OriginId)
  | .value environment (.call context arguments origin) => some (environment, context, arguments, origin)
  | _ => none

theorem valueCall_child_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (environment : RuntimeActivation) (context : Goose.Core.ContextId)
    (arguments : List Arg) (origin : Goose.Core.OriginId) (fuelEq : fuel = sourceFuel + 1)
    (operationEq : valueCallSyntax operation = some (environment, context, arguments, origin)) :
    (∀ id implementation lookupReady channels ready,
      getImplementation config context before = .ok (id, implementation) lookupReady →
      channelsFor config.layout environment.act implementation.results.toList origin lookupReady = .ok channels ready →
      SourceHistory config sourceFuel (path ++ [0]) (.channelCall environment context arguments channels origin) ready
        (invokeCall sourceFuel config environment context arguments channels origin ready)) ∨
    SourceHistory config sourceFuel (path ++ [0]) (.callWith environment context arguments origin) before
      (invokeCall sourceFuel config environment context arguments [] origin before) ∨
    (arguments = [] ∧ SourceHistory config sourceFuel (path ++ [0]) (.call environment context origin) before
      (invokeCall sourceFuel config environment context [] [] origin before)) := by
  cases history <;> simp_all [valueCallSyntax]
  case aggregate =>
    rename_i shape children
    cases shape <;> simp_all [valueCallSyntax]
  case logical =>
    rename_i isAnd first second left right
    cases isAnd <;> simp_all [valueCallSyntax, logicalExpression]
  case valueChannelCall =>
    left
    assumption
  case valueCall =>
    rename_i child
    right
    right
    have actual := child.sound
    simp only [execute] at actual
    rw [actual]
    exact child
  case valueCallWith =>
    rename_i child
    right
    left
    have actual := child.sound
    simp only [execute] at actual
    rw [actual]
    exact child

#print axioms valueCall_child_history
end Goose.Proofs.ConstructionGhostValueCallHistory
