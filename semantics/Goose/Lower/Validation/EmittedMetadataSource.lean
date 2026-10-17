import Goose.Lower.Validation.EmittedMetadataPrint
import Goose.Lower.Validation.EmittedMetadataStorageMutation
import Goose.Lower.Validation.EmittedMetadataControl
import Goose.Lower.Validation.EmittedMetadataControlEach

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem metadata_source_expression (expr : Expr) (env : Core.TEnv) (results : List Ty) :
    EmittedMetadataSourceExpression env results expr := by
  cases expr with
  | lit ty value =>
    exact metadata_source_literal env results ty value
  | bool value =>
    exact metadata_source_bool env results value
  | read place =>
    exact metadata_source_read place (metadata_source_place place env results)
  | ref mu place =>
    exact metadata_source_reference mu place (metadata_source_place place env results)
  | slice mu view lo hi origin =>
    exact metadata_source_slice mu view lo hi origin (metadata_source_view view env results)
      (metadata_source_bound lo env results) (metadata_source_bound hi env results)
  | len view =>
    exact metadata_source_length view (metadata_source_view view env results)
  | un op value origin =>
    exact metadata_source_unary op value origin (metadata_source_expression value env results)
  | bin op left right origin =>
    exact metadata_source_binary op left right origin
      (metadata_source_expression left env results) (metadata_source_expression right env results)
  | cmp op left right =>
    exact metadata_source_comparison op left right
      (metadata_source_expression left env results) (metadata_source_expression right env results)
  | and left right =>
    exact metadata_source_and left right
      (metadata_source_expression left env results) (metadata_source_expression right env results)
  | or left right =>
    exact metadata_source_or left right
      (metadata_source_expression left env results) (metadata_source_expression right env results)
  | not value =>
    exact metadata_source_not value (metadata_source_expression value env results)
  | conv kind ty value origin =>
    exact metadata_source_conversion kind ty value origin (metadata_source_expression value env results)
  | call context args origin =>
    exact metadata_source_call context args origin (metadata_source_argument_members args env results)
  | push owner value origin =>
    exact metadata_source_push owner value origin (metadata_source_place owner env results) (metadata_source_expression value env results)
  | pop owner origin =>
    exact metadata_source_pop owner origin (metadata_source_place owner env results)
  | ifE condition yes no =>
    exact metadata_source_ifExpression condition yes no (metadata_source_expression condition env results)
      (fun nextEnv => metadata_source_block yes nextEnv results) (fun nextEnv => metadata_source_block no nextEnv results)
  | blockE body =>
    exact metadata_source_blockExpression body (fun nextEnv => metadata_source_block body nextEnv results) env
  | arrLit ty exprs =>
    exact metadata_source_arrayLiteral ty exprs (metadata_source_expression_members exprs env results)
  | structLit ty exprs =>
    exact metadata_source_structLiteral ty exprs (metadata_source_expression_members exprs env results)
  | fill ty value =>
    exact metadata_source_fill ty value (metadata_source_expression value env results)
termination_by sizeOf expr

theorem metadata_source_expression_members (exprs : List Expr) (env : Core.TEnv) (results : List Ty) :
    ∀ expr ∈ exprs, EmittedMetadataSourceExpression env results expr := by
  cases exprs with
  | nil => intro expr member; cases member
  | cons head rest =>
    intro expr member
    rcases List.mem_cons.mp member with same | member
    · subst expr
      exact metadata_source_expression head env results
    · exact metadata_source_expression_members rest env results expr member
termination_by sizeOf exprs

theorem metadata_source_place (place : Place) (env : Core.TEnv) (results : List Ty) : EmittedMetadataSourcePlace env results place := by
  cases place with
  | var index =>
    exact metadata_source_variable env results index
  | global index =>
    exact metadata_source_global env results index
  | deref expr =>
    exact metadata_source_dereference expr (metadata_source_expression expr env results)
  | field owner index =>
    exact metadata_source_field owner index (metadata_source_place owner env results)
  | elem view index origin =>
    exact metadata_source_index view index origin
      (metadata_source_view view env results) (metadata_source_expression index env results)
termination_by sizeOf place

theorem metadata_source_view (view : View) (env : Core.TEnv) (results : List Ty) : EmittedMetadataSourceView env results view := by
  cases view with
  | of place =>
    exact metadata_source_view_of place (metadata_source_place place env results)
  | val expr =>
    exact metadata_source_view_val expr (metadata_source_expression expr env results)
termination_by sizeOf view

theorem metadata_source_bound (bound : Bound) (env : Core.TEnv) (results : List Ty) : EmittedMetadataSourceBound env results bound := by
  cases bound with
  | omitted =>
    exact metadata_source_bound_omitted env results
  | expr value =>
    exact metadata_source_bound_expr value (metadata_source_expression value env results)
  | fromEnd value =>
    exact metadata_source_bound_fromEnd value (metadata_source_expression value env results)
termination_by sizeOf bound

theorem metadata_source_argument_members (args : List Arg) (env : Core.TEnv) (results : List Ty) :
    ∀ arg ∈ args, EmittedMetadataSourceArgument env results arg := by
  cases args with
  | nil => intro arg member; cases member
  | cons head rest =>
    intro arg member
    rcases List.mem_cons.mp member with same | member
    · subst arg
      cases head with
      | byVal expr =>
        exact metadata_source_expression expr env results
      | byRef mu place =>
        exact metadata_source_place place env results
    · exact metadata_source_argument_members rest env results arg member
termination_by sizeOf args

theorem metadata_source_printExpressions (args : List PrintArg) (env : Core.TEnv) (results : List Ty) :
    ∀ expr, PrintArg.expr expr ∈ args → EmittedMetadataSourceExpression env results expr := by
  cases args with
  | nil => intro expr member; cases member
  | cons head rest =>
    intro expr member
    rcases List.mem_cons.mp member with same | member
    · cases head with
      | text text => cases same
      | expr value => cases same; exact metadata_source_expression expr env results
    · exact metadata_source_printExpressions rest env results expr member
termination_by sizeOf args

theorem metadata_source_block (block : Core.Block) (env : Core.TEnv) (results : List Ty) : EmittedMetadataSourceBlock env results block := by
  cases block with
  | mk scope stmts value =>
    apply metadata_source_block_parts scope stmts value
    · exact metadata_source_statement_members stmts results
    · intro expr same nextEnv
      cases value with
      | none => cases same
      | some value => cases same; exact metadata_source_expression expr nextEnv results
termination_by sizeOf block

theorem metadata_source_statement_members (stmts : List Stmt) (results : List Ty) :
    ∀ stmt ∈ stmts, ∀ env scope, EmittedMetadataSourceStatement env results scope stmt := by
  cases stmts with
  | nil => intro stmt member; cases member
  | cons head rest =>
    intro stmt member env scope
    rcases List.mem_cons.mp member with same | member
    · subst stmt
      exact metadata_source_statement head env results scope
    · exact metadata_source_statement_members rest results stmt member env scope
termination_by sizeOf stmts

theorem metadata_source_statement (stmt : Stmt) (env : Core.TEnv) (results : List Ty) (scope : ScopeId) :
    EmittedMetadataSourceStatement env results scope stmt := by
  cases stmt with
  | letS slot expr origin =>
    exact metadata_source_let scope slot expr origin (metadata_source_expression expr env results)
  | assign place expr origin =>
    exact metadata_source_assign scope place expr origin (metadata_source_place place env results) (metadata_source_expression expr env results)
  | assignOp op place expr origin =>
    exact metadata_source_assignOp scope op place expr origin (metadata_source_place place env results) (metadata_source_expression expr env results)
  | rebind slot expr origin =>
    exact metadata_source_rebind scope slot expr origin (metadata_source_expression expr env results)
  | append place view origin =>
    exact metadata_source_append scope place view origin (metadata_source_place place env results) (metadata_source_view view env results)
  | popN place expr origin =>
    exact metadata_source_popN scope place expr origin (metadata_source_place place env results) (metadata_source_expression expr env results)
  | clear place origin =>
    exact metadata_source_clear scope place origin (metadata_source_place place env results)
  | assignWhole place expr origin =>
    exact metadata_source_assignWhole scope place expr origin (metadata_source_place place env results) (metadata_source_expression expr env results)
  | resize place size fill origin =>
    apply metadata_source_resize scope place size fill origin (metadata_source_place place env results)
      (metadata_source_expression size env results)
    intro expr same
    cases fill with
    | none => cases same
    | some value => cases same; exact metadata_source_expression expr env results
  | expr value origin =>
    exact metadata_source_expressionStatement scope value origin (metadata_source_expression value env results)
  | ifS condition yes no origin =>
    apply metadata_source_conditional scope condition yes no origin (metadata_source_expression condition env results)
      (fun nextEnv => metadata_source_block yes nextEnv results)
    intro body same nextEnv
    cases no with
    | none => cases same
    | some value => cases same; exact metadata_source_block body nextEnv results
  | «while» condition body origin =>
    exact metadata_source_while scope condition body origin
      (metadata_source_expression condition env results) (fun nextEnv => metadata_source_block body nextEnv results)
  | forRange slot lo hi body origin =>
    exact metadata_source_forRange scope slot lo hi body origin
      (metadata_source_expression lo env results) (metadata_source_expression hi env results)
      (fun nextEnv => metadata_source_block body nextEnv results)
  | forEach slot index view byRef body origin =>
    exact metadata_source_forEach scope slot index view byRef body origin
      (metadata_source_view view env results) (fun nextEnv => metadata_source_block body nextEnv results)
  | ret value origin =>
    cases value with
    | none =>
      exact metadata_source_returnNone env results scope origin
    | some expr =>
      exact metadata_source_returnSome scope expr origin (metadata_source_expression expr env results)
  | brk origin =>
    exact metadata_source_break env results scope origin
  | cont origin =>
    exact metadata_source_continue env results scope origin
  | print args origin =>
    exact metadata_source_print scope args origin (metadata_source_printExpressions args env results)
  | assertS expr origin =>
    exact metadata_source_assert scope expr origin (metadata_source_expression expr env results)
  | abort kind origin =>
    exact metadata_source_abort env results scope kind origin
  | exit expr origin =>
    exact metadata_source_exit scope expr origin (metadata_source_expression expr env results)
termination_by sizeOf stmt

end

end Goose.Lower.Validation
