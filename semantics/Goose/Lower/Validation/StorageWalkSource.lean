import Goose.Lower.Validation.StorageWalkSourceBlocks
import Goose.Lower.Validation.StorageWalkSourceTransfers
import Goose.Lower.Validation.StorageWalkSourceControlStatements

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem storageWalk_source_expression (expr : Expr) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) :
    StorageWalkSourceExpression env results stack expr := by
  cases expr with
  | lit ty value =>
    exact storageWalk_source_literal env results stack ty value
  | bool value =>
    exact storageWalk_source_bool env results stack value
  | read place =>
    exact storageWalk_source_read place (storageWalk_source_place place env results stack)
  | ref mu place =>
    exact storageWalk_source_reference mu place (storageWalk_source_place place env results stack)
  | slice mu view lo hi origin =>
    exact storageWalk_source_slice mu view lo hi origin (storageWalk_source_view view env results stack)
      (storageWalk_source_bound lo env results stack) (storageWalk_source_bound hi env results stack)
  | len view =>
    exact storageWalk_source_length view (storageWalk_source_view view env results stack)
  | un op value origin =>
    exact storageWalk_source_unary op value origin (storageWalk_source_expression value env results stack)
  | bin op left right origin =>
    exact storageWalk_source_binary op left right origin
      (storageWalk_source_expression left env results stack) (storageWalk_source_expression right env results stack)
  | cmp op left right =>
    exact storageWalk_source_comparison op left right
      (storageWalk_source_expression left env results stack) (storageWalk_source_expression right env results stack)
  | and left right =>
    exact storageWalk_source_and left right
      (storageWalk_source_expression left env results stack) (storageWalk_source_expression right env results stack)
  | or left right =>
    exact storageWalk_source_or left right
      (storageWalk_source_expression left env results stack) (storageWalk_source_expression right env results stack)
  | not value =>
    exact storageWalk_source_not value (storageWalk_source_expression value env results stack)
  | conv kind ty value origin =>
    exact storageWalk_source_conversion kind ty value origin (storageWalk_source_expression value env results stack)
  | call context args origin =>
    exact storageWalk_source_call context args origin (storageWalk_source_argument_members args env results stack)
  | push owner value origin =>
    exact storageWalk_source_push owner value origin (storageWalk_source_place owner env results stack) (storageWalk_source_expression value env results stack)
  | pop owner origin =>
    exact storageWalk_source_pop owner origin (storageWalk_source_place owner env results stack)
  | ifE condition yes no =>
    exact storageWalk_source_ifExpression condition yes no (storageWalk_source_expression condition env results stack)
      (fun nextEnv => storageWalk_source_block yes nextEnv results stack) (fun nextEnv => storageWalk_source_block no nextEnv results stack)
  | blockE body =>
    exact storageWalk_source_blockExpression body (fun nextEnv => storageWalk_source_block body nextEnv results stack)
  | arrLit ty exprs =>
    exact storageWalk_source_arrayLiteral ty exprs (storageWalk_source_expression_members exprs env results stack)
  | structLit ty exprs =>
    exact storageWalk_source_structLiteral ty exprs (storageWalk_source_expression_members exprs env results stack)
  | fill ty value =>
    exact storageWalk_source_fill ty value (storageWalk_source_expression value env results stack)
termination_by sizeOf expr

theorem storageWalk_source_expression_members (exprs : List Expr) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) :
    ∀ expr ∈ exprs, StorageWalkSourceExpression env results stack expr := by
  cases exprs with
  | nil => intro expr member; cases member
  | cons head rest =>
    intro expr member
    rcases List.mem_cons.mp member with same | member
    · subst expr
      exact storageWalk_source_expression head env results stack
    · exact storageWalk_source_expression_members rest env results stack expr member
termination_by sizeOf exprs

theorem storageWalk_source_place (place : Place) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) : StorageWalkSourcePlace env results stack place := by
  cases place with
  | var index =>
    exact storageWalk_source_variable env results stack index
  | global index =>
    exact storageWalk_source_global env results stack index
  | deref expr =>
    exact storageWalk_source_dereference expr (storageWalk_source_expression expr env results stack)
  | field owner index =>
    exact storageWalk_source_field owner index (storageWalk_source_place owner env results stack)
  | elem view index origin =>
    exact storageWalk_source_index view index origin
      (storageWalk_source_view view env results stack) (storageWalk_source_expression index env results stack)
termination_by sizeOf place

theorem storageWalk_source_view (view : View) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) : StorageWalkSourceView env results stack view := by
  cases view with
  | of place =>
    exact storageWalk_source_view_of place (storageWalk_source_place place env results stack)
  | val expr =>
    exact storageWalk_source_view_val expr (storageWalk_source_expression expr env results stack)
termination_by sizeOf view

theorem storageWalk_source_eachSource (view : View) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) :
    StorageWalkSourceEachSource env results stack view := by
  cases view with
  | of place => exact storageWalk_source_eachSource_of place (storageWalk_source_place place env results stack)
  | val expr => exact storageWalk_source_eachSource_val expr (storageWalk_source_expression expr env results stack)
termination_by sizeOf view

theorem storageWalk_source_bound (bound : Bound) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) : StorageWalkSourceBound env results stack bound := by
  cases bound with
  | omitted =>
    exact storageWalk_source_bound_omitted env results stack
  | expr value =>
    exact storageWalk_source_bound_expr value (storageWalk_source_expression value env results stack)
  | fromEnd value =>
    exact storageWalk_source_bound_fromEnd value (storageWalk_source_expression value env results stack)
termination_by sizeOf bound

theorem storageWalk_source_argument_members (args : List Arg) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) :
    ∀ arg ∈ args, StorageWalkSourceArgument env results stack arg := by
  cases args with
  | nil => intro arg member; cases member
  | cons head rest =>
    intro arg member
    rcases List.mem_cons.mp member with same | member
    · subst arg
      cases head with
      | byVal expr =>
        exact storageWalk_source_expression expr env results stack
      | byRef mu place =>
        exact storageWalk_source_place place env results stack
    · exact storageWalk_source_argument_members rest env results stack arg member
termination_by sizeOf args

theorem storageWalk_source_printExpressions (args : List PrintArg) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) :
    ∀ expr, PrintArg.expr expr ∈ args → StorageWalkSourceExpression env results stack expr := by
  cases args with
  | nil => intro expr member; cases member
  | cons head rest =>
    intro expr member
    rcases List.mem_cons.mp member with same | member
    · cases head with
      | text text => cases same
      | expr value => cases same; exact storageWalk_source_expression expr env results stack
    · exact storageWalk_source_printExpressions rest env results stack expr member
termination_by sizeOf args

theorem storageWalk_source_block (block : Core.Block) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) : StorageWalkSourceBlock env results stack block := by
  cases block with
  | mk scope stmts value =>
    apply storageWalk_source_block_parts scope stmts value
    · exact storageWalk_source_statement_members stmts results (scope :: stack)
    · intro expr same nextEnv
      cases value with
      | none => cases same
      | some value => cases same; exact storageWalk_source_expression expr nextEnv results (scope :: stack)
termination_by sizeOf block

theorem storageWalk_source_statement_members (stmts : List Stmt) (results : List Ty) (stack : List ScopeId) :
    ∀ stmt ∈ stmts, ∀ env scope, StorageWalkSourceStatement env results stack scope stmt := by
  cases stmts with
  | nil => intro stmt member; cases member
  | cons head rest =>
    intro stmt member env scope
    rcases List.mem_cons.mp member with same | member
    · subst stmt
      exact storageWalk_source_statement head env results stack scope
    · exact storageWalk_source_statement_members rest results stack stmt member env scope
termination_by sizeOf stmts

theorem storageWalk_source_statement (stmt : Stmt) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) (scope : ScopeId) :
    StorageWalkSourceStatement env results stack scope stmt := by
  cases stmt with
  | letS slot expr origin =>
    exact storageWalk_source_let scope slot expr origin (storageWalk_source_expression expr env results stack)
  | assign place expr origin =>
    exact storageWalk_source_assign scope place expr origin (storageWalk_source_place place env results stack) (storageWalk_source_expression expr env results stack)
  | assignOp op place expr origin =>
    exact storageWalk_source_assignOp scope op place expr origin (storageWalk_source_place place env results stack) (storageWalk_source_expression expr env results stack)
  | rebind slot expr origin =>
    exact storageWalk_source_rebind scope slot expr origin (storageWalk_source_expression expr env results stack)
  | append place view origin =>
    exact storageWalk_source_append scope place view origin (storageWalk_source_place place env results stack) (storageWalk_source_view view env results stack)
  | popN place expr origin =>
    exact storageWalk_source_popN scope place expr origin (storageWalk_source_place place env results stack) (storageWalk_source_expression expr env results stack)
  | clear place origin =>
    exact storageWalk_source_clear scope place origin (storageWalk_source_place place env results stack)
  | assignWhole place expr origin =>
    exact storageWalk_source_assignWhole scope place expr origin (storageWalk_source_place place env results stack) (storageWalk_source_expression expr env results stack)
  | resize place size fill origin =>
    apply storageWalk_source_resize scope place size fill origin (storageWalk_source_place place env results stack)
      (storageWalk_source_expression size env results stack)
    intro expr same
    cases fill with
    | none => cases same
    | some value => cases same; exact storageWalk_source_expression expr env results stack
  | expr value origin =>
    exact storageWalk_source_expressionStatement scope value origin (storageWalk_source_expression value env results stack)
  | ifS condition yes no origin =>
    apply storageWalk_source_conditional scope condition yes no origin (storageWalk_source_expression condition env results stack)
      (fun nextEnv => storageWalk_source_block yes nextEnv results stack)
    intro body same nextEnv
    cases no with
    | none => cases same
    | some value => cases same; exact storageWalk_source_block body nextEnv results stack
  | «while» condition body origin =>
    exact storageWalk_source_while scope condition body origin
      (storageWalk_source_expression condition env results stack) (fun nextEnv => storageWalk_source_block body nextEnv results stack)
  | forRange slot lo hi body origin =>
    exact storageWalk_source_forRange scope slot lo hi body origin
      (storageWalk_source_expression lo env results stack) (storageWalk_source_expression hi env results stack)
      (fun nextEnv => storageWalk_source_block body nextEnv results stack)
  | forEach slot index view byRef body origin =>
    exact storageWalk_source_forEach scope slot index view byRef body origin
      (storageWalk_source_eachSource view env results stack) (fun nextEnv => storageWalk_source_block body nextEnv results stack)
  | ret value origin =>
    cases value with
    | none =>
      exact storageWalk_source_return scope none origin (by intro expr same; cases same)
    | some expr =>
      exact storageWalk_source_return scope (some expr) origin (by intro child same; cases same; exact storageWalk_source_expression expr env results stack)
  | brk origin =>
    exact storageWalk_source_break env results stack scope origin
  | cont origin =>
    exact storageWalk_source_continue env results stack scope origin
  | print args origin =>
    exact storageWalk_source_print scope args origin (storageWalk_source_printExpressions args env results stack)
  | assertS expr origin =>
    exact storageWalk_source_assert scope expr origin (storageWalk_source_expression expr env results stack)
  | abort kind origin =>
    exact storageWalk_source_abort env results stack scope kind origin
  | exit expr origin =>
    exact storageWalk_source_exit scope expr origin (storageWalk_source_expression expr env results stack)
termination_by sizeOf stmt

end

theorem storageWalk_source_argument_list (args : List Arg) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId)
    {callee : Core.Impl} {params : List Param} {start finish : Nat}
    (sameLength : params.length = args.length) (source : Core.tyArgs env callee params args start = .ok ((), finish))
    (visible : StorageWalkVisible env stack) (loop : Option LoopCtx) :
    StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerArgs args) :=
  storageWalk_source_arguments args visible loop sameLength source (storageWalk_source_argument_members args env results stack)

theorem storageWalk_source_expression_list (exprs : List Expr) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId)
    {types : List Ty} {start finish : Nat} (source : Core.tyStructExprs env types exprs start = .ok ((), finish))
    (visible : StorageWalkVisible env stack) (loop : Option LoopCtx) :
    StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerExprs exprs) :=
  storageWalk_source_expressions exprs visible loop source (storageWalk_source_expression_members exprs env results stack)

theorem storageWalk_source_statement_list (stmts : List Stmt) (env : Core.TEnv) (results : List Ty) (stack : List ScopeId)
    (scope : ScopeId) {output : Core.TEnv} {start finish : Nat}
    (source : Core.tyStmts env scope stmts start = .ok (output, finish))
    (visible : StorageWalkVisible env stack) (active : scope ∈ stack) (loop : Option LoopCtx) :
    StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerStmts loop stmts) :=
  storageWalk_source_statements scope stmts
    (fun stmt _member env => storageWalk_source_statement stmt env results stack scope) source visible active loop

#print axioms storageWalk_source_argument_list
#print axioms storageWalk_source_expression_list
#print axioms storageWalk_source_statement_list

#print axioms storageWalk_source_expression
#print axioms storageWalk_source_expression_members
#print axioms storageWalk_source_place
#print axioms storageWalk_source_view
#print axioms storageWalk_source_eachSource
#print axioms storageWalk_source_bound
#print axioms storageWalk_source_argument_members
#print axioms storageWalk_source_printExpressions
#print axioms storageWalk_source_block
#print axioms storageWalk_source_statement_members
#print axioms storageWalk_source_statement

end Goose.Lower.Validation
