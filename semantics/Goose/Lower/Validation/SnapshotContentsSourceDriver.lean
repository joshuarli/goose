import Goose.Lower.Validation.SnapshotContentsSourceControlEach
import Goose.Lower.Validation.SnapshotContentsSourceLeavesScalar
import Goose.Lower.Validation.SnapshotContentsSourceLeavesAccess
import Goose.Lower.Validation.SnapshotContentsSourceLeavesCollections
import Goose.Lower.Validation.SnapshotContentsSourceLeavesStorage
import Goose.Lower.Validation.SnapshotContentsSourceLeavesTransfers
import Goose.Lower.Validation.SnapshotContentsSourceControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem snapshot_source_expression (expr : Expr) (env : Core.TEnv) (results : List Ty) :
    SnapshotSourceExpression env results expr := by
  cases expr with
  | lit ty value =>
    exact snapshot_source_literal env results ty value
  | bool value =>
    exact snapshot_source_bool env results value
  | read place =>
    exact snapshot_source_read place (snapshot_source_place place env results)
  | ref mu place =>
    exact snapshot_source_reference mu place (snapshot_source_place place env results)
  | slice mu view lo hi origin =>
    exact snapshot_source_slice mu view lo hi origin (snapshot_source_view view env results)
      (snapshot_source_bound lo env results) (snapshot_source_bound hi env results)
  | len view =>
    exact snapshot_source_length view (snapshot_source_view view env results)
  | un op value origin =>
    exact snapshot_source_unary op value origin (snapshot_source_expression value env results)
  | bin op left right origin =>
    exact snapshot_source_binary op left right origin
      (snapshot_source_expression left env results) (snapshot_source_expression right env results)
  | cmp op left right =>
    exact snapshot_source_comparison op left right
      (snapshot_source_expression left env results) (snapshot_source_expression right env results)
  | and left right =>
    exact snapshot_source_and left right
      (snapshot_source_expression left env results) (snapshot_source_expression right env results)
  | or left right =>
    exact snapshot_source_or left right
      (snapshot_source_expression left env results) (snapshot_source_expression right env results)
  | not value =>
    exact snapshot_source_not value (snapshot_source_expression value env results)
  | conv kind ty value origin =>
    exact snapshot_source_conversion kind ty value origin (snapshot_source_expression value env results)
  | push owner value origin =>
    exact snapshot_source_push owner value origin
      (snapshot_source_place owner env results) (snapshot_source_expression value env results)
  | pop owner origin =>
    exact snapshot_source_pop owner origin (snapshot_source_place owner env results)
  | call context args origin =>
    exact snapshot_source_call context args origin (snapshot_source_argument_members args env results)
  | ifE condition yes no =>
    exact snapshot_source_ifExpression condition yes no (snapshot_source_expression condition env results)
      (fun nextEnv => snapshot_source_block yes nextEnv results) (fun nextEnv => snapshot_source_block no nextEnv results)
  | blockE body =>
    exact snapshot_source_blockExpression body (fun nextEnv => snapshot_source_block body nextEnv results) env
  | arrLit ty exprs =>
    exact snapshot_source_arrayLiteral ty exprs (snapshot_source_expression_members exprs env results)
  | structLit ty exprs =>
    exact snapshot_source_structLiteral ty exprs (snapshot_source_expression_members exprs env results)
  | fill ty value =>
    exact snapshot_source_fill ty value (snapshot_source_expression value env results)
termination_by sizeOf expr

theorem snapshot_source_expression_members (exprs : List Expr) (env : Core.TEnv) (results : List Ty) :
    ∀ expr ∈ exprs, SnapshotSourceExpression env results expr := by
  cases exprs with
  | nil => intro expr member; cases member
  | cons head rest =>
    intro expr member
    rcases List.mem_cons.mp member with same | member
    · subst expr
      exact snapshot_source_expression head env results
    · exact snapshot_source_expression_members rest env results expr member
termination_by sizeOf exprs

theorem snapshot_source_place (place : Place) (env : Core.TEnv) (results : List Ty) : SnapshotSourcePlace env results place := by
  cases place with
  | var index =>
    exact snapshot_source_variable env results index
  | global index =>
    exact snapshot_source_global env results index
  | deref expr =>
    exact snapshot_source_dereference expr (snapshot_source_expression expr env results)
  | field owner index =>
    exact snapshot_source_field owner index (snapshot_source_place owner env results)
  | elem view index origin =>
    exact snapshot_source_index view index origin
      (snapshot_source_view view env results) (snapshot_source_expression index env results)
termination_by sizeOf place

theorem snapshot_source_view (view : View) (env : Core.TEnv) (results : List Ty) : SnapshotSourceView env results view := by
  cases view with
  | of place =>
    exact snapshot_source_view_of place (snapshot_source_place place env results)
  | val expr =>
    exact snapshot_source_view_val expr (snapshot_source_expression expr env results)
termination_by sizeOf view

theorem snapshot_source_bound (bound : Bound) (env : Core.TEnv) (results : List Ty) : SnapshotSourceBound env results bound := by
  cases bound with
  | omitted =>
    exact snapshot_source_bound_omitted env results
  | expr value =>
    exact snapshot_source_bound_expr value (snapshot_source_expression value env results)
  | fromEnd value =>
    exact snapshot_source_bound_fromEnd value (snapshot_source_expression value env results)
termination_by sizeOf bound

theorem snapshot_source_argument_members (args : List Arg) (env : Core.TEnv) (results : List Ty) :
    ∀ arg ∈ args, SnapshotSourceArgument env results arg := by
  cases args with
  | nil => intro arg member; cases member
  | cons head rest =>
    intro arg member
    rcases List.mem_cons.mp member with same | member
    · subst arg
      cases head with
      | byVal expr =>
        exact snapshot_source_expression expr env results
      | byRef mu place =>
        exact snapshot_source_place place env results
    · exact snapshot_source_argument_members rest env results arg member
termination_by sizeOf args

theorem snapshot_source_printExpressions (args : List PrintArg) (env : Core.TEnv) (results : List Ty) :
    ∀ expr, PrintArg.expr expr ∈ args → SnapshotSourceExpression env results expr := by
  cases args with
  | nil => intro expr member; cases member
  | cons head rest =>
    intro expr member
    rcases List.mem_cons.mp member with same | member
    · cases head with
      | text text => cases same
      | expr value => cases same; exact snapshot_source_expression expr env results
    · exact snapshot_source_printExpressions rest env results expr member
termination_by sizeOf args

theorem snapshot_source_block (block : Core.Block) (env : Core.TEnv) (results : List Ty) : SnapshotSourceBlock env results block := by
  cases block with
  | mk scope stmts value =>
    apply snapshot_source_block_parts scope stmts value
    · exact snapshot_source_statement_members stmts results
    · intro expr same nextEnv
      cases value with
      | none => cases same
      | some value => cases same; exact snapshot_source_expression expr nextEnv results
termination_by sizeOf block

theorem snapshot_source_statement_members (stmts : List Stmt) (results : List Ty) :
    ∀ stmt ∈ stmts, ∀ env scope, SnapshotSourceStatement env results scope stmt := by
  cases stmts with
  | nil => intro stmt member; cases member
  | cons head rest =>
    intro stmt member env scope
    rcases List.mem_cons.mp member with same | member
    · subst stmt
      exact snapshot_source_statement head env results scope
    · exact snapshot_source_statement_members rest results stmt member env scope
termination_by sizeOf stmts

theorem snapshot_source_statement (stmt : Stmt) (env : Core.TEnv) (results : List Ty) (scope : ScopeId) :
    SnapshotSourceStatement env results scope stmt := by
  cases stmt with
  | letS slot expr origin =>
    exact snapshot_source_let scope slot expr origin (snapshot_source_expression expr env results)
  | assign place expr origin =>
    exact snapshot_source_assign scope place expr origin
      (snapshot_source_place place env results) (snapshot_source_expression expr env results)
  | assignOp op place expr origin =>
    exact snapshot_source_assignOp scope op place expr origin
      (snapshot_source_place place env results) (snapshot_source_expression expr env results)
  | rebind slot expr origin =>
    exact snapshot_source_rebind scope slot expr origin (snapshot_source_expression expr env results)
  | append place view origin =>
    exact snapshot_source_append scope place view origin
      (snapshot_source_place place env results) (snapshot_source_view view env results)
  | popN place expr origin =>
    exact snapshot_source_popN scope place expr origin
      (snapshot_source_place place env results) (snapshot_source_expression expr env results)
  | clear place origin =>
    exact snapshot_source_clear scope place origin (snapshot_source_place place env results)
  | assignWhole place expr origin =>
    exact snapshot_source_assignWhole scope place expr origin
      (snapshot_source_place place env results) (snapshot_source_expression expr env results)
  | resize place size fill origin =>
    apply snapshot_source_resize scope place size fill origin
      (snapshot_source_place place env results) (snapshot_source_expression size env results)
    intro expr same
    cases fill with
    | none => cases same
    | some value => cases same; exact snapshot_source_expression expr env results
  | expr value origin =>
    exact snapshot_source_expressionStatement scope value origin (snapshot_source_expression value env results)
  | ifS condition yes no origin =>
    apply snapshot_source_conditional scope condition yes no origin (snapshot_source_expression condition env results)
      (fun nextEnv => snapshot_source_block yes nextEnv results)
    intro body same nextEnv
    cases no with
    | none => cases same
    | some value => cases same; exact snapshot_source_block body nextEnv results
  | «while» condition body origin =>
    exact snapshot_source_while scope condition body origin
      (snapshot_source_expression condition env results) (fun nextEnv => snapshot_source_block body nextEnv results)
  | forRange slot lo hi body origin =>
    exact snapshot_source_forRange scope slot lo hi body origin
      (snapshot_source_expression lo env results) (snapshot_source_expression hi env results)
      (fun nextEnv => snapshot_source_block body nextEnv results)
  | forEach slot index view byRef body origin =>
    exact snapshot_source_forEach scope slot index view byRef body origin
      (snapshot_source_view view env results) (fun nextEnv => snapshot_source_block body nextEnv results)
  | ret value origin =>
    cases value with
    | none =>
      exact snapshot_source_returnNone env results scope origin
    | some expr =>
      exact snapshot_source_returnSome scope expr origin (snapshot_source_expression expr env results)
  | brk origin =>
    exact snapshot_source_break env results scope origin
  | cont origin =>
    exact snapshot_source_continue env results scope origin
  | print args origin =>
    exact snapshot_source_print scope args origin (snapshot_source_printExpressions args env results)
  | assertS expr origin =>
    exact snapshot_source_assert scope expr origin (snapshot_source_expression expr env results)
  | abort kind origin =>
    exact snapshot_source_abort env results scope kind origin
  | exit expr origin =>
    exact snapshot_source_exit scope expr origin (snapshot_source_expression expr env results)
termination_by sizeOf stmt

end

end Goose.Lower.Validation
