import Goose.Lower.Validation.StorageWalkSourceStorage
import Goose.Lower.Validation.StorageWalkControlBranches
import Goose.Lower.Validation.StorageWalkControlTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storageWalk_source_expressionStatement {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (expr : Expr) (origin : OriginId) (child : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceStatement env results stack scope (.expr expr origin) := by
  intro output start finish source visible active loop
  obtain ⟨type, childSource, _⟩ := tyStmt_expr_children source
  exact (child childSource visible loop).bind fun _ => StorageWalkAction.pure _ stack loop ()

theorem storageWalk_source_return {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (value : Option Expr) (origin : OriginId)
    (children : ∀ expr, value = some expr → StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceStatement env results stack scope (.ret value origin) := by
  intro output start finish source visible active loop
  cases value with
  | none =>
    exact (StorageWalkAction.pure _ stack loop []).bind fun values =>
      StorageWalkAction.unwindReturn _ stack loop values (some origin)
  | some expr =>
    obtain ⟨expected, actual, impl, inExpr, implAt, resultTypes, childSource, passing, _⟩ := tyStmt_return_children source
    exact ((children expr rfl childSource visible loop).bind fun value =>
      (StorageWalkAction.coerceResult _ stack loop value origin).bind fun coerced =>
        StorageWalkAction.pure _ stack loop [coerced]).bind fun values =>
          StorageWalkAction.unwindReturn _ stack loop values (some origin)

theorem storageWalk_source_break (env : Core.TEnv) (results : List Ty) (stack : List ScopeId)
    (scope : ScopeId) (origin : OriginId) : StorageWalkSourceStatement env results stack scope (.brk origin) := by
  intro output start finish source visible active loop
  cases loop with
  | none => exact StorageWalkAction.pure _ stack none ()
  | some context => exact StorageWalkAction.break _ stack context origin

theorem storageWalk_source_continue (env : Core.TEnv) (results : List Ty) (stack : List ScopeId)
    (scope : ScopeId) (origin : OriginId) : StorageWalkSourceStatement env results stack scope (.cont origin) := by
  intro output start finish source visible active loop
  cases loop with
  | none => exact StorageWalkAction.pure _ stack none ()
  | some context => exact StorageWalkAction.continue _ stack context origin

theorem storageWalk_printArguments (args : List PrintArg) (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx)
    (children : ∀ expr, PrintArg.expr expr ∈ args → StorageWalkAction slots stack loop (lowerExpr expr)) :
    StorageWalkAction slots stack loop (lowerPrintArgs args) := by
  induction args with
  | nil => exact StorageWalkAction.pure slots stack loop []
  | cons arg rest ih =>
    cases arg with
    | text text =>
      exact (ih (fun expr member => children expr (by simp [member]))).bind fun parts =>
        StorageWalkAction.pure slots stack loop (.text text :: parts)
    | expr expr =>
      exact (children expr (by simp)).bind fun value =>
        (ih (fun expr member => children expr (by simp [member]))).bind fun parts =>
          StorageWalkAction.pure slots stack loop (.val value :: parts)

theorem storageWalk_source_print {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (args : List PrintArg) (origin : OriginId)
    (children : ∀ expr, PrintArg.expr expr ∈ args → StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceStatement env results stack scope (.print args origin) := by
  intro output start finish source visible active loop
  have printSource := (tyStmt_print_children source).1
  have lowered := storageWalk_printArguments args (lowerEnv env.mod env.vars results).slots stack loop
    (fun expr member => by
      obtain ⟨type, childStart, childFinish, childSource, shape⟩ := tyPrintArgs_expr_children printSource member
      exact children expr member childSource visible loop)
  exact lowered.bind fun parts =>
    StorageWalkAction.emitEffect _ stack loop (.print parts (some origin)) rfl (by trivial)

theorem storageWalk_source_assert {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (expr : Expr) (origin : OriginId) (child : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceStatement env results stack scope (.assertS expr origin) := by
  intro output start finish source visible active loop
  exact (child (tyStmt_assert_children source).1 visible loop).bind fun value =>
    StorageWalkAction.assertCore value origin

theorem storageWalk_source_abort (env : Core.TEnv) (results : List Ty) (stack : List ScopeId)
    (scope : ScopeId) (message : String) (origin : OriginId) :
    StorageWalkSourceStatement env results stack scope (.abort message origin) := by
  intro output start finish source visible active loop
  exact StorageWalkAction.emitTerm _ stack loop (.abort .userAbort (some origin)) rfl
    (by intro entry target member; cases member) (by intro state target member; cases member)

theorem storageWalk_source_exit {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (expr : Expr) (origin : OriginId) (child : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceStatement env results stack scope (.exit expr origin) := by
  intro output start finish source visible active loop
  obtain ⟨integer, childSource, _⟩ := tyStmt_exit_children source
  exact (child childSource visible loop).bind fun value =>
    StorageWalkAction.emitTerm _ stack loop (.exit value (some origin)) rfl
      (by intro entry target member; cases member) (by intro state target member; cases member)

#print axioms storageWalk_source_expressionStatement
#print axioms storageWalk_source_return
#print axioms storageWalk_source_break
#print axioms storageWalk_source_continue
#print axioms storageWalk_printArguments
#print axioms storageWalk_source_print
#print axioms storageWalk_source_assert
#print axioms storageWalk_source_abort
#print axioms storageWalk_source_exit

end Goose.Lower.Validation
