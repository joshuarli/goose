import Goose.Lower.Validation.StorageWalkControlScope
import Goose.Lower.Validation.StorageWalkSourceStatements

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storageWalk_source_block_parts {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (stmts : List Stmt) (value : Option Expr)
    (stmtChildren : ∀ stmt ∈ stmts, ∀ env currentScope, StorageWalkSourceStatement env results (scope :: stack) currentScope stmt)
    (valueChild : ∀ expr, value = some expr → ∀ env, StorageWalkSourceExpression env results (scope :: stack) expr) :
    ∀ env, StorageWalkSourceBlock env results stack (.mk scope stmts value) := by
  intro env sourcePre type start finish source visible loop pre want preActive
  obtain ⟨_, declared, output, statementStart, valueStart, declaration, statements, finalValue⟩ :=
    tyBlock_checked_children source
  have scopedVisible : StorageWalkVisible {env with scopes := scope :: env.scopes} (scope :: stack) := visible
  have declaredVisible : StorageWalkVisible declared (scope :: stack) :=
    scopedVisible.declarePre (by simp) declaration
  have outputVisible := declaredVisible.tyStmts (by simp) statements
  have declaredTables := declarePre_tables sourcePre declaration
  have outputTables := tyStmts_tables stmts statements
  have sameDeclared : lowerEnv declared.mod declared.vars results = lowerEnv env.mod env.vars results := by
    rw [declaredTables.1, declaredTables.2.1]
  have sameOutput : lowerEnv output.mod output.vars results = lowerEnv env.mod env.vars results := by
    rw [outputTables.1, outputTables.2.1, sameDeclared]
  have stated := storageWalk_source_statements scope stmts (fun stmt member env => stmtChildren stmt member env scope)
    statements declaredVisible (by simp) loop
  rw [sameDeclared] at stated
  have valued : StorageWalkAction (lowerEnv env.mod env.vars results).slots (scope :: stack) loop (lowerBlockValue want value) := by
    cases value with
    | none =>
      cases want
      · exact StorageWalkAction.pure _ (scope :: stack) loop 0
      · exact StorageWalkAction.emitDef _ (scope :: stack) loop .constUnit (by intro result; trivial)
    | some expr =>
      have child := valueChild expr rfl output finalValue outputVisible loop
      rw [sameOutput] at child
      exact child
  have inside := (StorageWalkAction.initSlots _ (scope :: stack) loop pre preActive).bind fun _ =>
    stated.bind fun _ => valued
  simpa only [scopedAction_eq, lowerBlock, scope_bind_assoc] using StorageWalkAction.scoped scope inside

#print axioms storageWalk_source_block_parts

end Goose.Lower.Validation
