import Goose.Lower.Validation.EmittedTypingScalarSource
import Goose.Lower.Validation.EmittedTypingComparisonSource
import Goose.Lower.Validation.EmittedTypingBooleanSource
import Goose.Lower.Validation.EmittedTypingSliceSource
import Goose.Lower.Validation.EmittedTypingCallSource
import Goose.Lower.Validation.EmittedTypingAggregateSource
import Goose.Lower.Validation.EmittedTypingOwnerSource
import Goose.Lower.Validation.EmittedTypingConversionSource
import Goose.Lower.Validation.EmittedTypingExpressionBlocks
import Goose.Lower.Validation.EmittedTypingStorageSource
import Goose.Lower.Validation.EmittedTypingTransferSource
import Goose.Lower.Validation.EmittedTypingControlSource
import Goose.Lower.Validation.EmittedTypingEachSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem emitted_source_expression (expr : Expr) (env : Core.TEnv) (results : List Ty) :
    EmittedSourceExpression env results expr := by
  cases expr with
  | lit ty value =>
    exact emitted_source_literal env results ty value
  | bool value =>
    exact emitted_source_bool env results value
  | read place =>
    exact emitted_source_read place (emitted_source_place place env results)
  | ref mu place =>
    exact emitted_source_reference mu place (emitted_source_place place env results)
  | slice mu view lo hi origin =>
    exact emitted_source_slice mu view lo hi origin (emitted_source_view view env results)
      (emitted_source_bound lo env results) (emitted_source_bound hi env results)
  | len view =>
    exact emitted_source_length view (emitted_source_view view env results)
  | un op value origin =>
    exact emitted_source_unary (emitted_source_results env results) op value origin (emitted_source_expression value env results)
  | bin op left right origin =>
    exact emitted_source_binary (emitted_source_results env results) op left right origin
      (emitted_source_expression left env results) (emitted_source_expression right env results)
  | cmp op left right =>
    exact emitted_source_comparison op left right
      (emitted_source_expression left env results) (emitted_source_expression right env results)
  | and left right =>
    exact emitted_source_and left right
      (emitted_source_expression left env results) (emitted_source_expression right env results)
  | or left right =>
    exact emitted_source_or left right
      (emitted_source_expression left env results) (emitted_source_expression right env results)
  | not value =>
    exact emitted_source_not (emitted_source_results env results) value (emitted_source_expression value env results)
  | conv kind ty value origin =>
    intro type start finish source initial before generated builder
    exact emitted_checked_conversion_source (emitted_source_results env results) source
      (emitted_source_expression value env results) generated builder
  | call context args origin =>
    exact emitted_source_call context args origin (emitted_source_argument_members args env results)
  | push owner value origin =>
    intro type start finish source initial before generated builder
    exact emitted_checked_push_source (emitted_source_results env results) source
      (emitted_source_place owner env results) (emitted_source_expression value env results) generated builder
  | pop owner origin =>
    intro type start finish source initial before generated builder
    exact emitted_checked_pop_source (emitted_source_results env results) source
      (emitted_source_place owner env results) generated builder
  | ifE condition yes no =>
    exact emitted_source_ifExpression condition yes no (emitted_source_expression condition env results)
      (fun nextEnv => emitted_source_block yes nextEnv results) (fun nextEnv => emitted_source_block no nextEnv results)
  | blockE body =>
    exact emitted_source_blockExpression body (fun nextEnv => emitted_source_block body nextEnv results) env
  | arrLit ty exprs =>
    intro type start finish source initial before generated builder
    exact emitted_checked_arrayLiteral_source (emitted_source_results env results) exprs source
      (emitted_source_expressions exprs env results) generated builder
  | structLit ty exprs =>
    intro type start finish source initial before generated builder
    exact emitted_checked_structLiteral_source (emitted_source_results env results) exprs source
      (emitted_source_expressions exprs env results) generated builder
  | fill ty value =>
    intro type start finish source initial before generated builder
    exact emitted_checked_fill_source (emitted_source_results env results) value source
      (emitted_source_expression value env results) generated builder
termination_by sizeOf expr

theorem emitted_source_expressions (exprs : List Expr) (env : Core.TEnv) (results : List Ty) :
    ∀ expr ∈ exprs, EmittedSourceExpression env results expr := by
  cases exprs with
  | nil => intro expr member; cases member
  | cons head rest =>
    intro expr member
    rcases List.mem_cons.mp member with same | member
    · subst expr
      exact emitted_source_expression head env results
    · exact emitted_source_expressions rest env results expr member
termination_by sizeOf exprs

theorem emitted_source_place (place : Place) (env : Core.TEnv) (results : List Ty) : EmittedSourcePlace env results place := by
  cases place with
  | var index =>
    exact emitted_source_variable env results index
  | global index =>
    exact emitted_source_global env results index
  | deref expr =>
    exact emitted_source_dereference expr (emitted_source_expression expr env results)
  | field owner index =>
    exact emitted_source_field owner index (emitted_source_place owner env results)
  | elem view index origin =>
    exact emitted_source_index view index origin
      (emitted_source_view view env results) (emitted_source_expression index env results)
termination_by sizeOf place

theorem emitted_source_view (view : View) (env : Core.TEnv) (results : List Ty) : EmittedSourceView env results view := by
  cases view with
  | of place =>
    exact emitted_source_view_of place (emitted_source_place place env results)
  | val expr =>
    exact emitted_source_view_val expr (emitted_source_expression expr env results)
termination_by sizeOf view

theorem emitted_source_bound (bound : Bound) (env : Core.TEnv) (results : List Ty) : EmittedSourceBound env results bound := by
  cases bound with
  | omitted =>
    exact emitted_source_bound_omitted env results
  | expr value =>
    exact emitted_source_bound_expr value (emitted_source_expression value env results)
  | fromEnd value =>
    exact emitted_source_bound_fromEnd value (emitted_source_expression value env results)
termination_by sizeOf bound

theorem emitted_source_argument_members (args : List Arg) (env : Core.TEnv) (results : List Ty) :
    ∀ arg ∈ args, EmittedSourceArgument env results arg := by
  cases args with
  | nil => intro arg member; cases member
  | cons head rest =>
    intro arg member
    rcases List.mem_cons.mp member with same | member
    · subst arg
      cases head with
      | byVal expr =>
        exact emitted_source_expression expr env results
      | byRef mu place =>
        exact emitted_source_place place env results
    · exact emitted_source_argument_members rest env results arg member
termination_by sizeOf args

theorem emitted_source_printExpressions (args : List PrintArg) (env : Core.TEnv) (results : List Ty) :
    ∀ expr, PrintArg.expr expr ∈ args → EmittedSourceExpression env results expr := by
  cases args with
  | nil => intro expr member; cases member
  | cons head rest =>
    intro expr member
    rcases List.mem_cons.mp member with same | member
    · cases head with
      | text text => cases same
      | expr value => cases same; exact emitted_source_expression expr env results
    · exact emitted_source_printExpressions rest env results expr member
termination_by sizeOf args

theorem emitted_source_block (block : Core.Block) (env : Core.TEnv) (results : List Ty) : EmittedSourceBlock env results block := by
  cases block with
  | mk scope stmts value =>
    apply emitted_source_block_parts scope stmts value
    · exact emitted_source_statements stmts results
    · intro expr same nextEnv
      cases value with
      | none => cases same
      | some value => cases same; exact emitted_source_expression expr nextEnv results
termination_by sizeOf block

theorem emitted_source_statements (stmts : List Stmt) (results : List Ty) :
    ∀ stmt ∈ stmts, ∀ env scope, EmittedSourceStatement env results scope stmt := by
  cases stmts with
  | nil => intro stmt member; cases member
  | cons head rest =>
    intro stmt member env scope
    rcases List.mem_cons.mp member with same | member
    · subst stmt
      exact emitted_source_statement head env results scope
    · exact emitted_source_statements rest results stmt member env scope
termination_by sizeOf stmts

theorem emitted_source_statement (stmt : Stmt) (env : Core.TEnv) (results : List Ty) (scope : ScopeId) :
    EmittedSourceStatement env results scope stmt := by
  cases stmt with
  | letS slot expr origin =>
    intro output start finish source initial before loop generated builder loopTypes targets active
    exact (emitted_source_let source (emitted_source_expression expr env results) loop generated builder targets).1
  | assign place expr origin =>
    intro output start finish source initial before loop generated builder loopTypes targets active
    exact (emitted_source_assign source (emitted_source_place place env results) (emitted_source_expression expr env results) loop generated builder targets).1
  | assignOp op place expr origin =>
    intro output start finish source initial before loop generated builder loopTypes targets active
    exact (emitted_source_assignOp source (emitted_source_place place env results) (emitted_source_expression expr env results) loop generated builder targets).1
  | rebind slot expr origin =>
    intro output start finish source initial before loop generated builder loopTypes targets active
    exact (emitted_source_rebind source (emitted_source_expression expr env results) loop generated builder targets).1
  | append place view origin =>
    intro output start finish source initial before loop generated builder loopTypes targets active
    exact (emitted_source_append source (emitted_source_place place env results) (emitted_source_view view env results) loop generated builder targets).1
  | popN place expr origin =>
    intro output start finish source initial before loop generated builder loopTypes targets active
    exact (emitted_source_popN source (emitted_source_place place env results) (emitted_source_expression expr env results) loop generated builder targets).1
  | clear place origin =>
    intro output start finish source initial before loop generated builder loopTypes targets active
    exact (emitted_source_clear source (emitted_source_place place env results) loop generated builder targets).1
  | assignWhole place expr origin =>
    intro output start finish source initial before loop generated builder loopTypes targets active
    exact (emitted_source_assignWhole source (emitted_source_place place env results) (emitted_source_expression expr env results) loop generated builder targets).1
  | resize place size fill origin =>
    intro output start finish source initial before loop generated builder loopTypes targets active
    apply (emitted_source_resize source (emitted_source_place place env results)
      (emitted_source_expression size env results) ?_ loop generated builder targets).1
    intro expr same
    cases fill with
    | none => cases same
    | some value => cases same; exact emitted_source_expression expr env results
  | expr value origin =>
    exact emitted_source_expressionStatement scope value origin (emitted_source_expression value env results)
  | ifS condition yes no origin =>
    apply emitted_source_conditional scope condition yes no origin (emitted_source_expression condition env results)
      (fun nextEnv => emitted_source_block yes nextEnv results)
    intro body same nextEnv
    cases no with
    | none => cases same
    | some value => cases same; exact emitted_source_block body nextEnv results
  | «while» condition body origin =>
    exact emitted_source_while scope condition body origin
      (emitted_source_expression condition env results) (fun nextEnv => emitted_source_block body nextEnv results)
  | forRange slot lo hi body origin =>
    exact emitted_source_forRange scope slot lo hi body origin
      (emitted_source_expression lo env results) (emitted_source_expression hi env results)
      (fun nextEnv => emitted_source_block body nextEnv results)
  | forEach slot index view byRef body origin =>
    exact emitted_source_forEach scope slot index view byRef body origin
      (emitted_source_view view env results) (fun nextEnv => emitted_source_block body nextEnv results)
  | ret value origin =>
    cases value with
    | none =>
      exact emitted_source_returnNone env results scope origin
    | some expr =>
      exact emitted_source_returnSome scope expr origin (emitted_source_expression expr env results)
  | brk origin =>
    exact emitted_source_break env results scope origin
  | cont origin =>
    exact emitted_source_continue env results scope origin
  | print args origin =>
    exact emitted_source_print scope args origin (emitted_source_printExpressions args env results)
  | assertS expr origin =>
    exact emitted_source_assert scope expr origin (emitted_source_expression expr env results)
  | abort kind origin =>
    exact emitted_source_abort env results scope kind origin
  | exit expr origin =>
    exact emitted_source_exit scope expr origin (emitted_source_expression expr env results)
termination_by sizeOf stmt

end

end Goose.Lower.Validation
