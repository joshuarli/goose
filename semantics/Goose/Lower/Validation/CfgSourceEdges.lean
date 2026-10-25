import Goose.Lower.Validation.CfgSourceEdgeScalar
import Goose.Lower.Validation.CfgSourceEdgeAccess
import Goose.Lower.Validation.CfgSourceEdgeBoolean
import Goose.Lower.Validation.CfgSourceEdgeAggregates
import Goose.Lower.Validation.CfgSourceEdgeBlocks
import Goose.Lower.Validation.CfgSourceEdgeStorage
import Goose.Lower.Validation.CfgSourceEdgeTransfers
import Goose.Lower.Validation.CfgSourceEdgeControl
import Goose.Lower.Validation.CfgSourceEdgeEach

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem cfg_source_expression (expr : Expr) (env : Core.TEnv) (results : List Ty) :
    CfgSourceExpression env results expr := by
  cases expr with
  | lit ty value =>
    exact cfg_source_literal env results ty value
  | bool value =>
    exact cfg_source_boolean env results value
  | read place =>
    exact cfg_source_read place (cfg_source_place place env results)
  | ref mu place =>
    exact cfg_source_reference mu place (cfg_source_place place env results)
  | slice mu view lo hi origin =>
    exact cfg_source_slice mu view lo hi origin
      (cfg_source_view view env results) (cfg_source_bound lo env results) (cfg_source_bound hi env results)
  | len view =>
    exact cfg_source_length view (cfg_source_view view env results)
  | un op value origin =>
    exact cfg_source_unary op value origin (cfg_source_expression value env results)
  | bin op left right origin =>
    exact cfg_source_binary op left right origin
      (cfg_source_expression left env results) (cfg_source_expression right env results)
  | cmp op left right =>
    exact cfg_source_comparison op left right
      (cfg_source_expression left env results) (cfg_source_expression right env results)
  | and left right =>
    exact cfg_source_and left right (cfg_source_expression left env results) (cfg_source_expression right env results)
  | or left right =>
    exact cfg_source_or left right (cfg_source_expression left env results) (cfg_source_expression right env results)
  | not value =>
    exact cfg_source_not value (cfg_source_expression value env results)
  | conv kind ty value origin =>
    exact cfg_source_conversion kind ty value origin (cfg_source_expression value env results)
  | call context args origin =>
    exact cfg_source_call context args origin (cfg_source_arguments args env results)
  | push owner value origin =>
    exact cfg_source_push owner value origin
      (cfg_source_place owner env results) (cfg_source_expression value env results)
  | pop owner origin =>
    exact cfg_source_pop owner origin (cfg_source_place owner env results)
  | ifE condition yes no =>
    exact cfg_source_ifExpression condition yes no (cfg_source_expression condition env results)
      (cfg_source_block_all yes (Core.exprEnv env) results) (cfg_source_block_all no (Core.exprEnv env) results)
  | blockE body =>
    exact cfg_source_blockExpression body (cfg_source_block_all body (Core.exprEnv env) results)
  | arrLit ty exprs =>
    exact cfg_source_arrayLiteral ty exprs (cfg_source_expressions exprs env results)
  | structLit ty exprs =>
    exact cfg_source_structLiteral ty exprs (cfg_source_expressions exprs env results)
  | fill ty value =>
    exact cfg_source_fill ty value (cfg_source_expression value env results)
termination_by sizeOf expr

theorem cfg_source_expressions (exprs : List Expr) (env : Core.TEnv) (results : List Ty) :
    CfgSourceExpressions env results exprs := by
  cases exprs with
  | nil =>
    exact cfg_source_emptyExpressions env results
  | cons expr rest =>
    exact cfg_source_consExpressions expr rest
      (cfg_source_expression expr env results) (cfg_source_expressions rest env results)
termination_by sizeOf exprs

theorem cfg_source_place (place : Place) (env : Core.TEnv) (results : List Ty) : CfgSourcePlace env results place := by
  cases place with
  | var index =>
    exact cfg_source_variable env results index
  | global index =>
    exact cfg_source_global env results index
  | deref expr =>
    exact cfg_source_dereference expr (cfg_source_expression expr env results)
  | field owner index =>
    exact cfg_source_field owner index (cfg_source_place owner env results)
  | elem view index origin =>
    exact cfg_source_element view index origin
      (cfg_source_view view env results) (cfg_source_expression index env results)
termination_by sizeOf place

theorem cfg_source_view (view : View) (env : Core.TEnv) (results : List Ty) : CfgSourceView env results view := by
  cases view with
  | of place =>
    exact cfg_source_ownerView place (cfg_source_place place env results)
  | val expr =>
    exact cfg_source_valueView expr (cfg_source_expression expr env results)
termination_by sizeOf view

theorem cfg_source_eachSource (view : View) (env : Core.TEnv) (results : List Ty) : CfgSourceEachSource env results view := by
  cases view with
  | of place =>
    exact cfg_source_eachOwner place (cfg_source_place place env results)
  | val expr =>
    exact cfg_source_eachValue expr (cfg_source_expression expr env results)
termination_by sizeOf view

theorem cfg_source_bound (bound : Bound) (env : Core.TEnv) (results : List Ty) : CfgSourceBound env results bound := by
  cases bound with
  | omitted =>
    exact cfg_source_omittedBound env results
  | expr value =>
    exact cfg_source_expressionBound value (cfg_source_expression value env results)
  | fromEnd value =>
    exact cfg_source_endBound value (cfg_source_expression value env results)
termination_by sizeOf bound

theorem cfg_source_arguments (args : List Arg) (env : Core.TEnv) (results : List Ty) : CfgSourceArguments env results args := by
  cases args with
  | nil =>
    exact cfg_source_emptyArguments env results
  | cons arg rest =>
    cases arg with
    | byVal expr =>
      exact cfg_source_valueArgument expr rest (cfg_source_expression expr env results) (cfg_source_arguments rest env results)
    | byRef mu place =>
      exact cfg_source_referenceArgument mu place rest (cfg_source_place place env results) (cfg_source_arguments rest env results)
termination_by sizeOf args

theorem cfg_source_printArguments (args : List PrintArg) (env : Core.TEnv) (results : List Ty) : CfgSourcePrintArguments env results args := by
  cases args with
  | nil =>
    exact cfg_source_emptyPrintArguments env results
  | cons arg rest =>
    cases arg with
    | text value =>
      exact cfg_source_textPrintArgument value rest (cfg_source_printArguments rest env results)
    | expr value =>
      exact cfg_source_expressionPrintArgument value rest
        (cfg_source_expression value env results) (cfg_source_printArguments rest env results)
termination_by sizeOf args

theorem cfg_source_block_all (block : Core.Block) (env : Core.TEnv) (results : List Ty) : CfgSourceBlock env results block := by
  cases block with
  | mk scope stmts value =>
    apply cfg_source_block scope stmts value
    · exact fun nextEnv => cfg_source_statements stmts nextEnv results
    · intro nextEnv expr same
      cases value with
      | none => cases same
      | some value => cases same; exact cfg_source_expression expr nextEnv results
termination_by sizeOf block

theorem cfg_source_statements (stmts : List Stmt) (env : Core.TEnv) (results : List Ty) : CfgSourceStatements env results stmts := by
  cases stmts with
  | nil =>
    exact cfg_source_emptyStatements env results
  | cons stmt rest =>
    exact cfg_source_consStatements stmt rest
      (cfg_source_statement stmt env results) (fun nextEnv => cfg_source_statements rest nextEnv results)
termination_by sizeOf stmts

theorem cfg_source_statement (stmt : Stmt) (env : Core.TEnv) (results : List Ty) : CfgSourceStatement env results stmt := by
  cases stmt with
  | letS x expr origin =>
    exact cfg_source_let x expr origin (cfg_source_expression expr env results)
  | assign place expr origin =>
    exact cfg_source_assign place expr origin (cfg_source_place place env results) (cfg_source_expression expr env results)
  | assignOp op place expr origin =>
    exact cfg_source_assignOp op place expr origin (cfg_source_place place env results) (cfg_source_expression expr env results)
  | rebind x expr origin =>
    exact cfg_source_rebind x expr origin (cfg_source_expression expr env results)
  | expr value origin =>
    exact cfg_source_expressionStatement value origin (cfg_source_expression value env results)
  | append owner view origin =>
    exact cfg_source_append owner view origin (cfg_source_place owner env results) (cfg_source_view view env results)
  | popN owner count origin =>
    exact cfg_source_popN owner count origin (cfg_source_place owner env results) (cfg_source_expression count env results)
  | resize owner size fill origin =>
    apply cfg_source_resize owner size fill origin (cfg_source_place owner env results) (cfg_source_expression size env results)
    intro expr same
    cases fill with
    | none => cases same
    | some value => cases same; exact cfg_source_expression expr env results
  | clear owner origin =>
    exact cfg_source_clear owner origin (cfg_source_place owner env results)
  | assignWhole owner expr origin =>
    exact cfg_source_assignWhole owner expr origin (cfg_source_place owner env results) (cfg_source_expression expr env results)
  | ifS condition yes no origin =>
    apply cfg_source_ifStatement condition yes no origin (cfg_source_expression condition env results) (cfg_source_block_all yes env results)
    intro block same
    cases no with
    | none => cases same
    | some value => cases same; exact cfg_source_block_all block env results
  | «while» condition body origin =>
    exact cfg_source_while condition body origin (cfg_source_expression condition env results)
      (cfg_source_block_all body { env with loops := env.loops + 1 } results)
  | forRange x lo hi body origin =>
    exact cfg_source_range x lo hi body origin
      (cfg_source_expression lo env results) (cfg_source_expression hi env results)
      (cfg_source_block_all body { env with loops := env.loops + 1, visible := x :: env.visible } results)
  | forEach x index view byRef body origin =>
    exact cfg_source_each x index view byRef body origin (cfg_source_eachSource view env results)
      (cfg_source_block_all body { env with loops := env.loops + 1, visible := x :: index.toList ++ env.visible } results)
  | ret value origin =>
    cases value with
    | none =>
      exact cfg_source_returnUnit env results origin
    | some expr =>
      exact cfg_source_returnValue expr origin (cfg_source_expression expr env results)
  | brk origin =>
    exact cfg_source_break env results origin
  | cont origin =>
    exact cfg_source_continue env results origin
  | print args origin =>
    exact cfg_source_print args origin (cfg_source_printArguments args env results)
  | assertS expr origin =>
    exact cfg_source_assert expr origin (cfg_source_expression expr env results)
  | abort kind origin =>
    exact cfg_source_abort env results kind origin
  | exit expr origin =>
    exact cfg_source_exit expr origin (cfg_source_expression expr env results)
termination_by sizeOf stmt

end

end Goose.Lower.Validation
