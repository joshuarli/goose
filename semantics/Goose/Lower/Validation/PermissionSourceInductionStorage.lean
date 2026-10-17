import Goose.Lower.Validation.PermissionSourceInductionContracts
import Goose.Lower.Validation.PermissionInstructionStorageSource
import Goose.Lower.Validation.PermissionPreservationSimpleStatements
import Goose.Lower.Validation.PermissionPreservationPrintSource
import Goose.Lower.Validation.PermissionPreservationLoopExits

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem permission_source_let {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (slot : VarId) (expr : Expr) (origin : OriginId)
    (child0 : PermissionStorageExprChild env func results expr)
    : PermissionSourceStatement env func results scope (.letS slot expr origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_let_source tables.slots source child0 floor generated run

theorem permission_source_rebind {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (slot : VarId) (expr : Expr) (origin : OriginId)
    (child0 : PermissionStorageExprChild env func results expr)
    : PermissionSourceStatement env func results scope (.rebind slot expr origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_rebind_source source child0 floor generated run

theorem permission_source_assign {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (place : Place) (expr : Expr) (origin : OriginId)
    (child0 : PermissionStoragePlaceChild env func results place)
    (child1 : PermissionStorageExprChild env func results expr)
    : PermissionSourceStatement env func results scope (.assign place expr origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_assign_source source child0 child1 floor generated run

theorem permission_source_assignOp {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (op : BinOp) (place : Place) (expr : Expr) (origin : OriginId)
    (child0 : PermissionStoragePlaceChild env func results place)
    (child1 : PermissionStorageExprChild env func results expr)
    : PermissionSourceStatement env func results scope (.assignOp op place expr origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_assignOp_source source child0 child1 floor generated run

theorem permission_source_append {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (owner : Place) (view : View) (origin : OriginId)
    (child0 : PermissionStoragePlaceChild env func results owner)
    (child1 : PermissionStorageViewChild env func results view)
    : PermissionSourceStatement env func results scope (.append owner view origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_append_source source child0 child1 floor generated run

theorem permission_source_popN {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (owner : Place) (count : Expr) (origin : OriginId)
    (child0 : PermissionStoragePlaceChild env func results owner)
    (child1 : PermissionStorageExprChild env func results count)
    : PermissionSourceStatement env func results scope (.popN owner count origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_popN_source source child0 child1 floor generated run

theorem permission_source_clear {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (owner : Place) (origin : OriginId)
    (child0 : PermissionStoragePlaceChild env func results owner)
    : PermissionSourceStatement env func results scope (.clear owner origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_clear_source source child0 floor generated run

theorem permission_source_assignWhole {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (owner : Place) (expr : Expr) (origin : OriginId)
    (child0 : PermissionStoragePlaceChild env func results owner)
    (child1 : PermissionStorageExprChild env func results expr)
    : PermissionSourceStatement env func results scope (.assignWhole owner expr origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_assignWhole_source source child0 child1 floor generated run

theorem permission_source_resize {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (owner : Place) (count : Expr) (fill : Option Expr) (origin : OriginId)
    (placeChild : PermissionStoragePlaceChild env func results owner)
    (countChild : PermissionStorageExprChild env func results count)
    (fillChild : ∀ expr, fill = some expr → PermissionStorageExprChild env func results expr) :
    PermissionSourceStatement env func results scope (.resize owner count fill origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_resize_source source placeChild countChild fillChild floor generated run

theorem permission_source_return {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (value : Option Expr) (origin : OriginId)
    (children : ∀ expr, value = some expr → PermissionStorageExprChild env func results expr) :
    PermissionSourceStatement env func results scope (.ret value origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_return_source tables.results tables.implementationResults source children floor generated run

theorem permission_source_expressionStatement {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (expr : Expr) (origin : OriginId)
    (child : PermissionStorageExprChild env func results expr) :
    PermissionSourceStatement env func results scope (.expr expr origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_expression_source source run generated floor
    (fun type childStart childFinish typed value middle lowered => child typed generated lowered)

theorem permission_source_exit {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (expr : Expr) (origin : OriginId)
    (child : PermissionStorageExprChild env func results expr) :
    PermissionSourceStatement env func results scope (.exit expr origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_exit_source source run generated floor
    (fun type childStart childFinish typed value middle lowered => child typed generated lowered)

theorem permission_source_assert {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (expr : Expr) (origin : OriginId)
    (child : PermissionStorageExprChild env func results expr) :
    PermissionSourceStatement env func results scope (.assertS expr origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_assert_source source run generated floor
    (fun type childStart childFinish typed value middle lowered => child typed generated lowered)

theorem permission_source_abort {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (kind : String) (origin : OriginId) :
    PermissionSourceStatement env func results scope (.abort kind origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_abort run

theorem permission_source_break {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (origin : OriginId) : PermissionSourceStatement env func results scope (.brk origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_break run generated frames

theorem permission_source_continue {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (origin : OriginId) : PermissionSourceStatement env func results scope (.cont origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_continue run generated frames

theorem permission_source_print {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (args : List PrintArg) (origin : OriginId)
    (children : ∀ expr, PrintArg.expr expr ∈ args → PermissionStorageExprChild env func results expr) :
    PermissionSourceStatement env func results scope (.print args origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  exact permissionInstructions_print_source source run generated floor
    (fun expr member type childStart childFinish typed before after value generated floor lowered =>
      (children expr member typed generated lowered).weaken floor)

#print axioms permission_source_let
#print axioms permission_source_rebind
#print axioms permission_source_assign
#print axioms permission_source_assignOp
#print axioms permission_source_append
#print axioms permission_source_popN
#print axioms permission_source_clear
#print axioms permission_source_assignWhole
#print axioms permission_source_resize
#print axioms permission_source_return
#print axioms permission_source_expressionStatement
#print axioms permission_source_exit
#print axioms permission_source_assert
#print axioms permission_source_abort
#print axioms permission_source_break
#print axioms permission_source_continue
#print axioms permission_source_print

end Goose.Lower.Validation
