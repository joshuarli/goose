import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem profile_source_expression (expr : Expr) (env : Core.TEnv) (results : List Ty) :
    EmittedProfileSourceExpression env results expr := by
  cases expr with
  | lit ty value =>
    exact profile_source_literal env results ty value
  | bool value =>
    exact profile_source_bool env results value
  | read place =>
    exact profile_source_read place (profile_source_place place env results)
  | ref mu place =>
    exact profile_source_reference mu place (profile_source_place place env results)
  | slice mu view lo hi origin =>
    exact profile_source_slice mu view lo hi origin (profile_source_view view env results)
      (profile_source_bound lo env results) (profile_source_bound hi env results)
  | len view =>
    exact profile_source_length view (profile_source_view view env results)
  | un op value origin =>
    exact profile_source_unary op value origin (profile_source_expression value env results)
  | bin op left right origin =>
    exact profile_source_binary op left right origin
      (profile_source_expression left env results) (profile_source_expression right env results)
  | cmp op left right =>
    exact profile_source_comparison op left right
      (profile_source_expression left env results) (profile_source_expression right env results)
  | and left right =>
    exact profile_source_and left right
      (profile_source_expression left env results) (profile_source_expression right env results)
  | or left right =>
    exact profile_source_or left right
      (profile_source_expression left env results) (profile_source_expression right env results)
  | not value =>
    exact profile_source_not value (profile_source_expression value env results)
  | conv kind ty value origin =>
    exact profile_source_conversion kind ty value origin (profile_source_expression value env results)
  | call context args origin =>
    exact profile_source_call context args origin (profile_source_argument_members args env results)
  | push owner value origin =>
    exact profile_source_push owner value origin (profile_source_place owner env results) (profile_source_expression value env results)
  | pop owner origin =>
    exact profile_source_pop owner origin (profile_source_place owner env results)
  | ifE condition yes no =>
    exact profile_source_ifExpression condition yes no (profile_source_expression condition env results)
      (fun nextEnv => profile_source_block yes nextEnv results) (fun nextEnv => profile_source_block no nextEnv results)
  | blockE body =>
    exact profile_source_blockExpression body (fun nextEnv => profile_source_block body nextEnv results) env
  | arrLit ty exprs =>
    exact profile_source_arrayLiteral ty exprs (profile_source_expression_members exprs env results)
  | structLit ty exprs =>
    exact profile_source_structLiteral ty exprs (profile_source_expression_members exprs env results)
  | fill ty value =>
    exact profile_source_fill ty value (profile_source_expression value env results)
termination_by sizeOf expr

theorem profile_source_expression_members (exprs : List Expr) (env : Core.TEnv) (results : List Ty) :
    ∀ expr ∈ exprs, EmittedProfileSourceExpression env results expr := by
  cases exprs with
  | nil => intro expr member; cases member
  | cons head rest =>
    intro expr member
    rcases List.mem_cons.mp member with same | member
    · subst expr
      exact profile_source_expression head env results
    · exact profile_source_expression_members rest env results expr member
termination_by sizeOf exprs

theorem profile_source_place (place : Place) (env : Core.TEnv) (results : List Ty) : EmittedProfileSourcePlace env results place := by
  cases place with
  | var index =>
    exact profile_source_variable env results index
  | global index =>
    exact profile_source_global env results index
  | deref expr =>
    exact profile_source_dereference expr (profile_source_expression expr env results)
  | field owner index =>
    exact profile_source_field owner index (profile_source_place owner env results)
  | elem view index origin =>
    exact profile_source_index view index origin
      (profile_source_view view env results) (profile_source_expression index env results)
termination_by sizeOf place

theorem profile_source_view (view : View) (env : Core.TEnv) (results : List Ty) : EmittedProfileSourceView env results view := by
  cases view with
  | of place =>
    exact profile_source_view_of place (profile_source_place place env results)
  | val expr =>
    exact profile_source_view_val expr (profile_source_expression expr env results)
termination_by sizeOf view

theorem profile_source_bound (bound : Bound) (env : Core.TEnv) (results : List Ty) : EmittedProfileSourceBound env results bound := by
  cases bound with
  | omitted =>
    exact profile_source_bound_omitted env results
  | expr value =>
    exact profile_source_bound_expr value (profile_source_expression value env results)
  | fromEnd value =>
    exact profile_source_bound_fromEnd value (profile_source_expression value env results)
termination_by sizeOf bound

theorem profile_source_argument_members (args : List Arg) (env : Core.TEnv) (results : List Ty) :
    ∀ arg ∈ args, EmittedProfileSourceArgument env results arg := by
  cases args with
  | nil => intro arg member; cases member
  | cons head rest =>
    intro arg member
    rcases List.mem_cons.mp member with same | member
    · subst arg
      cases head with
      | byVal expr =>
        exact profile_source_expression expr env results
      | byRef mu place =>
        exact profile_source_place place env results
    · exact profile_source_argument_members rest env results arg member
termination_by sizeOf args

theorem profile_source_printExpressions (args : List PrintArg) (env : Core.TEnv) (results : List Ty) :
    ∀ expr, PrintArg.expr expr ∈ args → EmittedProfileSourceExpression env results expr := by
  cases args with
  | nil => intro expr member; cases member
  | cons head rest =>
    intro expr member
    rcases List.mem_cons.mp member with same | member
    · cases head with
      | text text => cases same
      | expr value => cases same; exact profile_source_expression expr env results
    · exact profile_source_printExpressions rest env results expr member
termination_by sizeOf args

theorem profile_source_block (block : Core.Block) (env : Core.TEnv) (results : List Ty) : EmittedProfileSourceBlock env results block := by
  cases block with
  | mk scope stmts value =>
    apply profile_source_block_parts scope stmts value
    · exact profile_source_statement_members stmts results
    · intro expr same nextEnv
      cases value with
      | none => cases same
      | some value => cases same; exact profile_source_expression expr nextEnv results
termination_by sizeOf block

theorem profile_source_statement_members (stmts : List Stmt) (results : List Ty) :
    ∀ stmt ∈ stmts, ∀ env scope, EmittedProfileSourceStatement env results scope stmt := by
  cases stmts with
  | nil => intro stmt member; cases member
  | cons head rest =>
    intro stmt member env scope
    rcases List.mem_cons.mp member with same | member
    · subst stmt
      exact profile_source_statement head env results scope
    · exact profile_source_statement_members rest results stmt member env scope
termination_by sizeOf stmts

theorem profile_source_statement (stmt : Stmt) (env : Core.TEnv) (results : List Ty) (scope : ScopeId) :
    EmittedProfileSourceStatement env results scope stmt := by
  cases stmt with
  | letS slot expr origin =>
    exact profile_source_let scope slot expr origin (profile_source_expression expr env results)
  | assign place expr origin =>
    exact profile_source_assign scope place expr origin (profile_source_place place env results) (profile_source_expression expr env results)
  | assignOp op place expr origin =>
    exact profile_source_assignOp scope op place expr origin (profile_source_place place env results) (profile_source_expression expr env results)
  | rebind slot expr origin =>
    exact profile_source_rebind scope slot expr origin (profile_source_expression expr env results)
  | append place view origin =>
    exact profile_source_append scope place view origin (profile_source_place place env results) (profile_source_view view env results)
  | popN place expr origin =>
    exact profile_source_popN scope place expr origin (profile_source_place place env results) (profile_source_expression expr env results)
  | clear place origin =>
    exact profile_source_clear scope place origin (profile_source_place place env results)
  | assignWhole place expr origin =>
    exact profile_source_assignWhole scope place expr origin (profile_source_place place env results) (profile_source_expression expr env results)
  | resize place size fill origin =>
    apply profile_source_resize scope place size fill origin (profile_source_place place env results)
      (profile_source_expression size env results)
    intro expr same
    cases fill with
    | none => cases same
    | some value => cases same; exact profile_source_expression expr env results
  | expr value origin =>
    exact profile_source_expressionStatement scope value origin (profile_source_expression value env results)
  | ifS condition yes no origin =>
    apply profile_source_conditional scope condition yes no origin (profile_source_expression condition env results)
      (fun nextEnv => profile_source_block yes nextEnv results)
    intro body same nextEnv
    cases no with
    | none => cases same
    | some value => cases same; exact profile_source_block body nextEnv results
  | «while» condition body origin =>
    exact profile_source_while scope condition body origin
      (profile_source_expression condition env results) (fun nextEnv => profile_source_block body nextEnv results)
  | forRange slot lo hi body origin =>
    exact profile_source_forRange scope slot lo hi body origin
      (profile_source_expression lo env results) (profile_source_expression hi env results)
      (fun nextEnv => profile_source_block body nextEnv results)
  | forEach slot index view byRef body origin =>
    exact profile_source_forEach scope slot index view byRef body origin
      (profile_source_view view env results) (fun nextEnv => profile_source_block body nextEnv results)
  | ret value origin =>
    cases value with
    | none =>
      exact profile_source_returnNone env results scope origin
    | some expr =>
      exact profile_source_returnSome scope expr origin (profile_source_expression expr env results)
  | brk origin =>
    exact profile_source_break env results scope origin
  | cont origin =>
    exact profile_source_continue env results scope origin
  | print args origin =>
    exact profile_source_print scope args origin (profile_source_printExpressions args env results)
  | assertS expr origin =>
    exact profile_source_assert scope expr origin (profile_source_expression expr env results)
  | abort kind origin =>
    exact profile_source_abort env results scope kind origin
  | exit expr origin =>
    exact profile_source_exit scope expr origin (profile_source_expression expr env results)
termination_by sizeOf stmt

end

end Goose.Lower.Validation
