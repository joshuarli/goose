import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostValueBlockHistory
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual

def valueBlockSyntax : SourceOperation α → Option (RuntimeActivation × Block × Goose.Core.OriginId)
  | .value environment (.blockE block origin) => some (environment, block, origin)
  | _ => none

def valueBlockTailSyntax : SourceOperation α → Option (RuntimeActivation × Nat × List Stmt × Expr)
  | .block environment (.mk scope statements (some expression)) => some (environment, scope, statements, expression)
  | _ => none

theorem valueBlock_child_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (block : Block) (origin : Goose.Core.OriginId)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : valueBlockSyntax operation = some (environment, block, origin)) :
    SourceHistory config sourceFuel (path ++ [0]) (.block environment block) before (execBlock sourceFuel config environment [] [] block before) := by
  cases history <;> simp_all [valueBlockSyntax]
  case aggregate =>
    rename_i shape children
    cases shape <;> simp_all [valueBlockSyntax]
  case logical =>
    rename_i isAnd first second left right
    cases isAnd <;> simp_all [valueBlockSyntax, logicalExpression]

theorem valueBlock_body_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (scope : Nat) (statements : List Stmt) (expression : Expr)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : valueBlockTailSyntax operation = some (environment, scope, statements, expression)) :
    SourceHistory config sourceFuel (path ++ [0])
      (.statements { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements)
      { before with nextScope := before.nextScope + 1 }
      (execStmts sourceFuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements
        { before with nextScope := before.nextScope + 1 }) := by
  cases history <;> simp_all [valueBlockTailSyntax]

theorem valueBlock_tail_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (scope : Nat) (statements : List Stmt) (expression : Expr)
    (value : Value) (ready : ExecutionState) (fuelEq : fuel = sourceFuel + 1)
    (operationEq : valueBlockTailSyntax operation = some (environment, scope, statements, expression))
    (body : execStmts sourceFuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements
      { before with nextScope := before.nextScope + 1 } = .ok (.normal value) ready) :
    SourceHistory config sourceFuel (path ++ [1])
      (.value { environment with scopes := (scope, before.nextScope) :: environment.scopes } expression) ready
      (evalValue sourceFuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } expression ready) := by
  cases history <;> simp only [valueBlockTailSyntax, reduceCtorEq] at operationEq
  case timeout => cases fuelEq
  case blockTail =>
    rename_i actualFuel actualEnvironment actualScope actualStatements actualExpression bodyChild tailChild
    simp only [Option.some.injEq, Prod.mk.injEq] at operationEq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := operationEq
    cases fuelEq
    exact tailChild value ready body

#print axioms valueBlock_tail_history
#print axioms valueBlock_child_history
#print axioms valueBlock_body_history
end Goose.Proofs.ConstructionGhostValueBlockHistory
