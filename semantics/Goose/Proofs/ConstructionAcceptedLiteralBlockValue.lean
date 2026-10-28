import Goose.Proofs.ConstructionAcceptedLiteralBlockQuery

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem evalValue_integerBlock_of_produce (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (scope : Nat) (statements : List Stmt) (ty : Goose.Core.IntTy) (literal : Int) (origin : Nat)
    (before after : ExecutionState) (value : Value)
    (produced : evalProduce fuel config environment [.register (.int ty)]
      (.blockE ⟨scope, statements, some (.lit ty literal)⟩ origin) before = .ok [.register value] after) :
    evalValue (fuel + 1) config environment (.blockE ⟨scope, statements, some (.lit ty literal)⟩ origin) before =
      .ok value after := by
  have query := blockResultTypes_integerTail fuel ⟨config.module, environment.vars⟩ scope statements ty literal
  simp only at query
  simp [evalValue, query, channelsFor, Ty.nonfixed, bind, pure, produced, publishCarriers,
    liftConstruction, publishOperation, preflightPublication, ConstructionM.get, Except.bind, Except.pure, singleCarrier, carrierValue]

theorem evalValue_integerBlock_of_produceStop (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (scope : Nat) (statements : List Stmt) (ty : Goose.Core.IntTy) (literal : Int) (origin : Nat)
    (before after : ExecutionState) (reason : Goose.Core.Stop)
    (produced : evalProduce fuel config environment [.register (.int ty)]
      (.blockE ⟨scope, statements, some (.lit ty literal)⟩ origin) before = .stop reason after) :
    evalValue (fuel + 1) config environment (.blockE ⟨scope, statements, some (.lit ty literal)⟩ origin) before =
      .stop reason after := by
  have query := blockResultTypes_integerTail fuel ⟨config.module, environment.vars⟩ scope statements ty literal
  simp only at query
  simp [evalValue, query, channelsFor, Ty.nonfixed, bind, pure, produced]

#print axioms evalValue_integerBlock_of_produceStop
#print axioms evalValue_integerBlock_of_produce
end Goose.Proofs.ConstructionAcceptedExecution
