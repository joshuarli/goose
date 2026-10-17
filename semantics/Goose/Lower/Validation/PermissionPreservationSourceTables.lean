import Goose.Lower.Validation.SourceEnvironment

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure PermissionSourceTables (env : Core.TEnv) (resultTypes : List Ty) (func : Func) : Prop where
  slots : func.slots = (lowerEnv env.mod env.vars resultTypes).slots
  results : func.results = resultTypes
  implementationResults : ∀ impl, env.impl = some impl → resultTypes = impl.results.toList

theorem PermissionSourceTables.retained {env after : Core.TEnv} {resultTypes : List Ty} {func : Func}
    (tables : PermissionSourceTables env resultTypes func)
    (vars : after.vars = env.vars) (implementation : after.impl = env.impl) :
    PermissionSourceTables after resultTypes func := by
  constructor
  · simpa only [lowerEnv, vars] using tables.slots
  · exact tables.results
  · intro impl row
    exact tables.implementationResults impl (by rw [← implementation]; exact row)

theorem PermissionSourceTables.tyStmt {env after : Core.TEnv} {resultTypes : List Ty} {func : Func}
    {scope start finish : Nat} {stmt : Stmt} (tables : PermissionSourceTables env resultTypes func)
    (source : Core.tyStmt env scope stmt start = .ok (after, finish)) :
    PermissionSourceTables after resultTypes func := by
  have same := tyStmt_tables stmt source
  exact tables.retained same.2.1 same.2.2

theorem PermissionSourceTables.tyStmts {env after : Core.TEnv} {resultTypes : List Ty} {func : Func}
    {scope start finish : Nat} {stmts : List Stmt} (tables : PermissionSourceTables env resultTypes func)
    (source : Core.tyStmts env scope stmts start = .ok (after, finish)) :
    PermissionSourceTables after resultTypes func := by
  have same := tyStmts_tables stmts source
  exact tables.retained same.2.1 same.2.2

theorem PermissionSourceTables.declarePre {env after : Core.TEnv} {resultTypes : List Ty} {func : Func}
    {scope start finish : Nat} {pre : List (VarId × Ty)} (tables : PermissionSourceTables env resultTypes func)
    (source : Core.declarePre env scope pre start = .ok (after, finish)) :
    PermissionSourceTables after resultTypes func := by
  have same := declarePre_tables pre source
  exact tables.retained same.2.1 same.2.2

#print axioms PermissionSourceTables.retained
#print axioms PermissionSourceTables.tyStmts

end Goose.Lower.Validation
