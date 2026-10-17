import Goose.Lower.Validation.EmittedTypingBlockSource
import Goose.Lower.Validation.EmittedTypingStatements
import Goose.Lower.Validation.EmittedTypingMutationStatements
import Goose.Lower.Validation.EmittedTypingBranches
import Goose.Lower.Validation.SourceStatementTypingTransfers
import Goose.Lower.Validation.OperandSource

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_source_expressionStatement {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : EmittedSourceExpression env results expr) :
    EmittedSourceStatement env results scope (.expr expr origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  obtain ⟨type, childSource, _⟩ := tyStmt_expr_children source
  exact emitted_checked_lowerStmt_expression loop expr origin (child childSource generated builder)

theorem emitted_source_returnNone (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (origin : OriginId) :
    EmittedSourceStatement env results scope (.ret none origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  exact emitted_checked_lowerStmt_return_none loop origin builder

theorem emitted_source_returnSome {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : EmittedSourceExpression env results expr) :
    EmittedSourceStatement env results scope (.ret (some expr) origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  obtain ⟨expected, actual, impl, _, _, _, childSource, _, _⟩ := tyStmt_return_children source
  exact emitted_checked_lowerStmt_return_some loop expr origin (child childSource generated builder)

theorem emitted_source_break (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (origin : OriginId) :
    EmittedSourceStatement env results scope (.brk origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  exact emitted_checked_lowerStmt_break builder loop origin

theorem emitted_source_continue (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (origin : OriginId) :
    EmittedSourceStatement env results scope (.cont origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  exact emitted_checked_lowerStmt_continue builder loop loopTypes origin

theorem emitted_source_abort (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (message : String) (origin : OriginId) :
    EmittedSourceStatement env results scope (.abort message origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  exact emitted_checked_lowerStmt_abort builder loop message origin

theorem emitted_source_exit {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : EmittedSourceExpression env results expr) :
    EmittedSourceStatement env results scope (.exit expr origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  obtain ⟨integer, childSource, _⟩ := tyStmt_exit_children source
  exact emitted_checked_lowerStmt_exit loop expr origin (child childSource generated builder)

theorem emitted_source_assert {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (expr : Expr) (origin : OriginId) (child : EmittedSourceExpression env results expr) :
    EmittedSourceStatement env results scope (.assertS expr origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  have checked := child (tyStmt_assert_children source).1 generated builder
  exact emitted_checked_assert checked (lowerExpr expr (lowerEnv env.mod env.vars results) before).1 origin
    (value_lowerExpr expr _ _ _ _ rfl)

theorem emitted_checked_printArguments {le : LEnv} (args : List PrintArg)
    (children : ∀ expr, PrintArg.expr expr ∈ args → ∀ {initial before : LS},
      GeneratedBuilderState before → EmittedBuilder le initial before → EmittedBuilder le initial (lowerExpr expr le before).2)
    {initial before : LS} (generated : GeneratedBuilderState before) (builder : EmittedBuilder le initial before) :
    EmittedBuilder le initial (lowerPrintArgs args le before).2 := by
  induction args generalizing before with
  | nil => exact builder
  | cons arg rest inductionHypothesis =>
    cases arg with
    | text text =>
      exact inductionHypothesis (fun expr member => children expr (by simp [member])) generated builder
    | expr expr =>
      have child := children expr (by simp) generated builder
      have childGenerated : GeneratedBuilderState (lowerExpr expr le before).2 := generated.lowerExpr expr rfl
      exact inductionHypothesis (fun expr member => children expr (by simp [member])) childGenerated child

theorem emitted_source_print {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (args : List PrintArg) (origin : OriginId)
    (children : ∀ expr, PrintArg.expr expr ∈ args → EmittedSourceExpression env results expr) :
    EmittedSourceStatement env results scope (.print args origin) := by
  intro output start finish source initial before loop generated builder loopTypes loopBounds active
  have printSource := (tyStmt_print_children source).1
  have partsBuilder := emitted_checked_printArguments args (fun expr member {initial before} generated builder => by
    obtain ⟨type, childStart, childFinish, childSource, _⟩ := tyPrintArgs_expr_children printSource member
    exact children expr member childSource generated builder) generated builder
  apply partsBuilder.emitEffect (.print (lowerPrintArgs args (lowerEnv env.mod env.vars results) before).1 (some origin))
  intro live operand member
  exact values_lowerPrintArgs args _ before _ _ rfl live operand (by simpa [Effect.uses] using member)

end Goose.Lower.Validation
