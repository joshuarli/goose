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

theorem PermissionSourceTables.lowerImpl {env : Core.TEnv} (impl : Core.Impl)
    (vars : env.vars = impl.vars) (implementation : env.impl = some impl) :
    PermissionSourceTables env impl.results.toList (lowerImpl env.mod impl) := by
  constructor
  · change (lowerEnv env.mod impl.vars impl.results.toList).slots =
      (lowerEnv env.mod env.vars impl.results.toList).slots
    rw [vars]
  · rfl
  · intro actual row
    have same : impl = actual := Option.some.inj (implementation.symm.trans row)
    subst actual
    rfl

theorem PermissionSourceTables.lowerContextAt {env : Core.TEnv} (context : Core.Context) (impl : Core.Impl)
    (vars : env.vars = impl.vars) (implementation : env.impl = some impl) :
    PermissionSourceTables env impl.results.toList (lowerContextAt env.mod context impl) :=
  by
    have tables := PermissionSourceTables.lowerImpl impl vars implementation
    exact ⟨tables.slots, tables.results, tables.implementationResults⟩

theorem PermissionSourceTables.lowerGlobal {env : Core.TEnv} (global : Core.Global)
    (vars : env.vars = #[]) (implementation : env.impl = none) :
    PermissionSourceTables env [global.ty] (lowerGlobal env.mod global).init := by
  constructor
  · change (lowerEnv env.mod #[] [global.ty]).slots = (lowerEnv env.mod env.vars [global.ty]).slots
    rw [vars]
  · rfl
  · intro actual impossible
    rw [implementation] at impossible
    cases impossible

#print axioms PermissionSourceTables.lowerImpl
#print axioms PermissionSourceTables.lowerGlobal

#print axioms PermissionSourceTables.retained
#print axioms PermissionSourceTables.tyStmts

end Goose.Lower.Validation
