import Goose.Proofs.ConstructionGhostDeclarationOnce

namespace Goose.Proofs.ConstructionGhostDeclarationInversion
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostDeclarationOnce

def declarationSyntax : SourceOperation α → Option (RuntimeActivation × Goose.Core.VarId × Expr × Goose.Core.OriginId)
  | .statement environment (.letS localVar expression origin) => some (environment, localVar, expression, origin)
  | _ => none

theorem fixed_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
    (expression : Expr) (origin : Goose.Core.OriginId) (descriptor : LocalVar)
    (root : Goose.Core.RootInst) (ready : ExecutionState)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : declarationSyntax operation = some (environment, localVar, expression, origin))
    (found : environment.vars[localVar]? = some descriptor) (fixed : descriptor.ty.nonfixed = false)
    (rootResult : rootOf environment localVar before = .ok root ready) :
    SourceHistory config sourceFuel (path ++ [0]) (.value environment expression) ready
      (evalValue sourceFuel config environment expression ready) := by
  cases history <;> simp_all [declarationSyntax]
  case valueFirstStatement =>
    rename_i shape child
    cases shape <;> simp_all [declarationSyntax]
  case leafStatement =>
    rename_i shape
    cases shape <;> simp_all [declarationSyntax]

theorem occurrence_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome)
    (sourceFuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
    (expression : Expr) (origin : Goose.Core.OriginId) (destination : Option Goose.Core.DestinationId) (ready : ExecutionState)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : declarationSyntax operation = some (environment, localVar, expression, origin))
    (occurrence : DeclarationOccurrence sourceFuel config environment localVar expression origin before destination ready) :
    match destination with
    | none => SourceHistory config sourceFuel (path ++ [0]) (.value environment expression) ready
        (evalValue sourceFuel config environment expression ready)
    | some destination => SourceHistory config sourceFuel (path ++ [0]) (.builder environment destination expression) ready
        (buildExpr sourceFuel config environment destination expression ready) := by
  cases history <;> simp_all [declarationSyntax]
  case valueFirstStatement =>
    rename_i shape child
    cases shape <;> simp_all [declarationSyntax]
  case leafStatement =>
    rename_i shape
    cases shape <;> simp_all [declarationSyntax]
  case declaration =>
    cases occurrence <;> simp_all
    case direct => apply_assumption <;> first | assumption | rfl
    case named =>
      rename_i named
      apply named <;> first | assumption | rfl

#print axioms occurrence_history
#print axioms fixed_history
end Goose.Proofs.ConstructionGhostDeclarationInversion
