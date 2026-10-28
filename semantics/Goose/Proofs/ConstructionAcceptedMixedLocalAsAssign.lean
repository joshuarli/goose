import Goose.Proofs.ConstructionAcceptedMixedLocalExecution
import Goose.Proofs.ConstructionAcceptedMixedAssignExecution

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem MixedLocalStatements.asAssign {statements : List Stmt} (form : MixedLocalStatements statements) :
    MixedAssignStatements statements := by
  induction form with
  | nil => exact .nil
  | scalar expression origin rest accepted tail ih => exact .scalar expression origin rest accepted ih
  | byte declaration rest tail ih => exact .byte declaration rest ih
  | scalarLocal id expression origin rest accepted tail ih => exact .scalarLocal id expression origin rest accepted ih

theorem MixedLocalStatements.noAssignment {statements : List Stmt} (form : MixedLocalStatements statements) :
    ∀ place expression origin, .assign place expression origin ∉ statements := by
  induction form with
  | nil => simp
  | scalar expression origin rest accepted tail ih => simp [ih]
  | byte declaration rest tail ih => simp [ByteOwnerDeclaration.statement, ih]
  | scalarLocal id expression origin rest accepted tail ih => simp [ih]

#print axioms MixedLocalStatements.asAssign
#print axioms MixedLocalStatements.noAssignment
end Goose.Proofs.ConstructionAcceptedExecution
