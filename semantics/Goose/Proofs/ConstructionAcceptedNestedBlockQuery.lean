import Goose.Proofs.ConstructionAcceptedLiteralBlockValue

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem blockResultTypes_nestedIntegerTail (fuel : Nat) (environment : DeclarationEnv)
    (outerScope innerScope id origin innerOrigin : Nat) (expression : Expr) (ty : Goose.Core.IntTy) (value : Int) :
    let block : Block := ⟨outerScope, [], some (.blockE ⟨innerScope, [.assign (.global id) expression origin], some (.lit ty value)⟩ innerOrigin)⟩
    blockResultTypes? (max fuel (blockQueryBudget block)) environment block = some [.int ty] := by
  let block : Block := ⟨outerScope, [], some (.blockE ⟨innerScope, [.assign (.global id) expression origin], some (.lit ty value)⟩ innerOrigin)⟩
  have enough : 4 ≤ max fuel (blockQueryBudget block) := by
    apply Nat.le_trans _ (Nat.le_max_right _ _)
    simp only [block, blockQueryBudget, expressionQueryBudget]
    omega
  obtain ⟨other, same⟩ := Nat.exists_eq_add_of_le enough
  change blockResultTypes? (max fuel (blockQueryBudget block)) environment block = some [.int ty]
  rw [same, Nat.add_comm 4 other]
  simp [block, blockResultTypes?, expressionResultTypes?, DeclarationEnv.exprType?]

theorem evalValue_nestedIntegerBlock_of_produce (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (outerScope innerScope id origin innerOrigin outerOrigin : Nat) (expression : Expr) (ty : Goose.Core.IntTy) (literal : Int)
    (before after : ExecutionState) (value : Value)
    (produced : evalProduce fuel config environment [.register (.int ty)]
      (.blockE ⟨outerScope, [], some (.blockE ⟨innerScope, [.assign (.global id) expression origin], some (.lit ty literal)⟩ innerOrigin)⟩ outerOrigin) before = .ok [.register value] after) :
    evalValue (fuel + 1) config environment (.blockE ⟨outerScope, [], some (.blockE
      ⟨innerScope, [.assign (.global id) expression origin], some (.lit ty literal)⟩ innerOrigin)⟩ outerOrigin) before = .ok value after := by
  have query := blockResultTypes_nestedIntegerTail fuel ⟨config.module, environment.vars⟩ outerScope innerScope id origin innerOrigin expression ty literal
  simp only at query
  simp [evalValue, query, channelsFor, Ty.nonfixed, bind, pure, produced, publishCarriers,
    liftConstruction, publishOperation, preflightPublication, ConstructionM.get, Except.bind, Except.pure, singleCarrier, carrierValue]

theorem evalValue_nestedIntegerBlock_of_produceStop (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (outerScope innerScope id origin innerOrigin outerOrigin : Nat) (expression : Expr) (ty : Goose.Core.IntTy) (literal : Int)
    (before after : ExecutionState) (reason : Goose.Core.Stop)
    (produced : evalProduce fuel config environment [.register (.int ty)]
      (.blockE ⟨outerScope, [], some (.blockE ⟨innerScope, [.assign (.global id) expression origin], some (.lit ty literal)⟩ innerOrigin)⟩ outerOrigin) before = .stop reason after) :
    evalValue (fuel + 1) config environment (.blockE ⟨outerScope, [], some (.blockE
      ⟨innerScope, [.assign (.global id) expression origin], some (.lit ty literal)⟩ innerOrigin)⟩ outerOrigin) before = .stop reason after := by
  have query := blockResultTypes_nestedIntegerTail fuel ⟨config.module, environment.vars⟩ outerScope innerScope id origin innerOrigin expression ty literal
  simp only at query
  simp [evalValue, query, channelsFor, Ty.nonfixed, bind, pure, produced]

#print axioms blockResultTypes_nestedIntegerTail
#print axioms evalValue_nestedIntegerBlock_of_produce
#print axioms evalValue_nestedIntegerBlock_of_produceStop
end Goose.Proofs.ConstructionAcceptedExecution
