import Goose.Lower.Validation.PermissionSourceInductionStorage
import Goose.Lower.Validation.PermissionSourceInductionControlBlocks
import Goose.Lower.Validation.PermissionSourceInductionControlLoops
import Goose.Lower.Validation.PermissionSourceInductionEach

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

mutual

theorem permission_source_expression (expr : Expr) (env : Core.TEnv) (func : Func) (results : List Ty) (tables : PermissionSourceTables env results func) :
    PermissionStorageExprChild env func results expr := by
  cases expr with
  | lit ty value =>
    exact permission_source_literal env func results ty value
  | bool value =>
    exact permission_source_bool env func results value
  | read place =>
    exact permission_source_read place (permission_source_place place env func results tables)
  | ref mu place =>
    exact permission_source_reference mu place (permission_source_place place env func results tables)
  | slice mu view lo hi origin =>
    exact permission_source_slice mu view lo hi origin (permission_source_view view env func results tables)
      (permission_source_bound lo env func results tables) (permission_source_bound hi env func results tables)
  | len view =>
    exact permission_source_length view (permission_source_view view env func results tables)
  | un op value origin =>
    exact permission_source_unary op value origin (permission_source_expression value env func results tables)
  | bin op left right origin =>
    exact permission_source_binary op left right origin
      (permission_source_expression left env func results tables) (permission_source_expression right env func results tables)
  | cmp op left right =>
    exact permission_source_comparison op left right
      (permission_source_expression left env func results tables) (permission_source_expression right env func results tables)
  | and left right =>
    exact permission_source_and left right
      (permission_source_expression left env func results tables) (permission_source_expression right env func results tables)
  | or left right =>
    exact permission_source_or left right
      (permission_source_expression left env func results tables) (permission_source_expression right env func results tables)
  | not value =>
    exact permission_source_not value (permission_source_expression value env func results tables)
  | conv kind ty value origin =>
    exact permission_source_conversion kind ty value origin (permission_source_expression value env func results tables)
  | call context args origin =>
    exact permission_source_call context args origin (permission_source_argument_members args env func results tables)
  | push owner value origin =>
    exact permission_source_push owner value origin (permission_source_place owner env func results tables) (permission_source_expression value env func results tables)
  | pop owner origin =>
    exact permission_source_pop owner origin (permission_source_place owner env func results tables)
  | ifE condition yes no =>
    exact permission_source_ifExpression condition yes no tables (permission_source_expression condition env func results tables)
      (fun nextEnv => permission_source_block yes nextEnv func results) (fun nextEnv => permission_source_block no nextEnv func results)
  | blockE body =>
    exact permission_source_blockExpression body tables (fun nextEnv => permission_source_block body nextEnv func results)
  | arrLit ty exprs =>
    exact permission_source_arrayLiteral ty exprs (permission_source_expression_members exprs env func results tables)
  | structLit ty exprs =>
    exact permission_source_structLiteral ty exprs (permission_source_expression_members exprs env func results tables)
  | fill ty value =>
    exact permission_source_fill ty value (permission_source_expression value env func results tables)
termination_by sizeOf expr

theorem permission_source_expression_members (exprs : List Expr) (env : Core.TEnv) (func : Func) (results : List Ty) (tables : PermissionSourceTables env results func) :
    ∀ expr ∈ exprs, PermissionStorageExprChild env func results expr := by
  cases exprs with
  | nil => intro expr member; cases member
  | cons head rest =>
    intro expr member
    rcases List.mem_cons.mp member with same | member
    · subst expr
      exact permission_source_expression head env func results tables
    · exact permission_source_expression_members rest env func results tables expr member
termination_by sizeOf exprs

theorem permission_source_place (place : Place) (env : Core.TEnv) (func : Func) (results : List Ty) (tables : PermissionSourceTables env results func) : PermissionStoragePlaceChild env func results place := by
  cases place with
  | var index =>
    exact permission_source_variable env func results index
  | global index =>
    exact permission_source_global env func results index
  | deref expr =>
    exact permission_source_dereference expr (permission_source_expression expr env func results tables)
  | field owner index =>
    exact permission_source_field owner index (permission_source_place owner env func results tables)
  | elem view index origin =>
    exact permission_source_index view index origin
      (permission_source_view view env func results tables) (permission_source_expression index env func results tables)
termination_by sizeOf place

theorem permission_source_view (view : View) (env : Core.TEnv) (func : Func) (results : List Ty) (tables : PermissionSourceTables env results func) : PermissionStorageViewChild env func results view := by
  cases view with
  | of place =>
    exact permission_source_view_of place (permission_source_place place env func results tables)
  | val expr =>
    exact permission_source_view_val expr (permission_source_expression expr env func results tables)
termination_by sizeOf view

theorem permission_source_bound (bound : Bound) (env : Core.TEnv) (func : Func) (results : List Ty) (tables : PermissionSourceTables env results func) : PermissionSourceBound env func results bound := by
  cases bound with
  | omitted => exact permission_source_bound_omitted env func results
  | expr value => exact permission_source_bound_expr value (permission_source_expression value env func results tables)
  | fromEnd value => exact permission_source_bound_fromEnd value (permission_source_expression value env func results tables)
termination_by sizeOf bound

theorem permission_source_argument_members (args : List Arg) (env : Core.TEnv) (func : Func) (results : List Ty) (tables : PermissionSourceTables env results func) :
    ∀ arg ∈ args, PermissionSourceArgument env func results arg := by
  cases args with
  | nil => intro arg member; cases member
  | cons head rest =>
    intro arg member
    rcases List.mem_cons.mp member with same | member
    · subst arg
      cases head with
      | byVal expr =>
        exact permission_source_expression expr env func results tables
      | byRef mu place =>
        exact permission_source_place place env func results tables
    · exact permission_source_argument_members rest env func results tables arg member
termination_by sizeOf args

theorem permission_source_printExpressions (args : List PrintArg) (env : Core.TEnv) (func : Func) (results : List Ty) (tables : PermissionSourceTables env results func) :
    ∀ expr, PrintArg.expr expr ∈ args → PermissionStorageExprChild env func results expr := by
  cases args with
  | nil => intro expr member; cases member
  | cons head rest =>
    intro expr member
    rcases List.mem_cons.mp member with same | member
    · cases head with
      | text text => cases same
      | expr value => cases same; exact permission_source_expression expr env func results tables
    · exact permission_source_printExpressions rest env func results tables expr member
termination_by sizeOf args

theorem permission_source_block (block : Core.Block) (env : Core.TEnv) (func : Func) (results : List Ty) : PermissionSourceBlock env func results block := by
  cases block with
  | mk scope stmts value =>
    apply permission_source_block_parts scope stmts value
    · exact permission_source_statement_members stmts func results
    · intro expr same nextEnv
      cases value with
      | none => cases same
      | some value => cases same; exact permission_source_expression expr nextEnv func results
termination_by sizeOf block

theorem permission_source_statement_members (stmts : List Stmt) (func : Func) (results : List Ty) :
    ∀ stmt ∈ stmts, ∀ env scope, PermissionSourceStatement env func results scope stmt := by
  cases stmts with
  | nil => intro stmt member; cases member
  | cons head rest =>
    intro stmt member env scope
    rcases List.mem_cons.mp member with same | member
    · subst stmt
      exact permission_source_statement head env func results scope
    · exact permission_source_statement_members rest func results stmt member env scope
termination_by sizeOf stmts

theorem permission_source_statement (stmt : Stmt) (env : Core.TEnv) (func : Func) (results : List Ty) (scope : ScopeId) :
    PermissionSourceStatement env func results scope stmt := by
  intro tables
  cases stmt with
  | letS slot expr origin =>
    exact permission_source_let scope slot expr origin (permission_source_expression expr env func results tables) tables
  | assign place expr origin =>
    exact permission_source_assign scope place expr origin (permission_source_place place env func results tables) (permission_source_expression expr env func results tables) tables
  | assignOp op place expr origin =>
    exact permission_source_assignOp scope op place expr origin (permission_source_place place env func results tables) (permission_source_expression expr env func results tables) tables
  | rebind slot expr origin =>
    exact permission_source_rebind scope slot expr origin (permission_source_expression expr env func results tables) tables
  | append place view origin =>
    exact permission_source_append scope place view origin (permission_source_place place env func results tables) (permission_source_view view env func results tables) tables
  | popN place expr origin =>
    exact permission_source_popN scope place expr origin (permission_source_place place env func results tables) (permission_source_expression expr env func results tables) tables
  | clear place origin =>
    exact permission_source_clear scope place origin (permission_source_place place env func results tables) tables
  | assignWhole place expr origin =>
    exact permission_source_assignWhole scope place expr origin (permission_source_place place env func results tables) (permission_source_expression expr env func results tables) tables
  | resize place size fill origin =>
    refine permission_source_resize scope place size fill origin (permission_source_place place env func results tables)
      (permission_source_expression size env func results tables) ?_ tables
    intro expr same
    cases fill with
    | none => cases same
    | some value => cases same; exact permission_source_expression expr env func results tables
  | expr value origin =>
    exact permission_source_expressionStatement scope value origin (permission_source_expression value env func results tables) tables
  | ifS condition yes no origin =>
    refine permission_source_conditional scope condition yes no origin (permission_source_expression condition env func results tables)
      (fun nextEnv => permission_source_block yes nextEnv func results) ?_ tables
    intro body same nextEnv
    cases no with
    | none => cases same
    | some value => cases same; exact permission_source_block body nextEnv func results
  | «while» condition body origin =>
    exact permission_source_while scope condition body origin
      (permission_source_expression condition env func results tables) (fun nextEnv => permission_source_block body nextEnv func results) tables
  | forRange slot lo hi body origin =>
    exact permission_source_forRange scope slot lo hi body origin
      (permission_source_expression lo env func results tables) (permission_source_expression hi env func results tables)
      (fun nextEnv => permission_source_block body nextEnv func results) tables
  | forEach slot index view byRef body origin =>
    exact permission_source_forEach scope slot index view byRef body origin
      (permission_source_view view env func results tables) (fun nextEnv => permission_source_block body nextEnv func results) tables
  | ret value origin =>
    cases value with
    | none =>
      exact permission_source_return scope none origin (by intro expr same; cases same) tables
    | some expr =>
      exact permission_source_return scope (some expr) origin (by intro child same; cases same; exact permission_source_expression expr env func results tables) tables
  | brk origin =>
    exact permission_source_break scope origin tables
  | cont origin =>
    exact permission_source_continue scope origin tables
  | print args origin =>
    exact permission_source_print scope args origin (permission_source_printExpressions args env func results tables) tables
  | assertS expr origin =>
    exact permission_source_assert scope expr origin (permission_source_expression expr env func results tables) tables
  | abort kind origin =>
    exact permission_source_abort scope kind origin tables
  | exit expr origin =>
    exact permission_source_exit scope expr origin (permission_source_expression expr env func results tables) tables
termination_by sizeOf stmt

end

theorem permission_source_arguments (args : List Arg) (env : Core.TEnv) (func : Func) (results : List Ty)
    (tables : PermissionSourceTables env results func) {callee : Core.Impl} {params : List Param}
    {start finish : Nat} (sameLength : params.length = args.length)
    (source : Core.tyArgs env callee params args start = .ok ((), finish))
    {before after : LS} {values : List ValueId} (generated : GeneratedBuilderState before)
    (run : lowerArgs args (lowerEnv env.mod env.vars results) before = (values, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) before.vals.size before after := by
  exact newPermissions_lowerArgs args sameLength source (Nat.le_refl _)
    (fun expr member type start finish typed before middle value generated lowered =>
      permission_source_expression expr env func results tables typed generated lowered)
    (fun requested place member info start finish typed before middle value generated lowered =>
      permission_source_place place env func results tables typed generated lowered) generated run

theorem permission_source_argument (arg : Arg) (env : Core.TEnv) (func : Func) (results : List Ty)
    (tables : PermissionSourceTables env results func) {callee : Core.Impl} {param : Param}
    {params : List Param} {rest : List Arg} {start finish : Nat}
    (source : Core.tyArgs env callee (param :: params) (arg :: rest) start = .ok ((), finish))
    {before after : LS} {value : ValueId} (generated : GeneratedBuilderState before)
    (run : lowerArg arg (lowerEnv env.mod env.vars results) before = (value, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) before.vals.size before after := by
  cases arg with
  | byVal expr =>
    obtain ⟨localVar, type, childStart, childFinish, restStart, row, typed, passing, remaining⟩ :=
      tyArgs_byVal_head source
    exact permission_source_expression expr env func results tables typed generated run
  | byRef requested place =>
    exact newPermissions_lowerArg_byRef source (Nat.le_refl _)
      (fun info next typed before middle value generated lowered =>
        permission_source_place place env func results tables typed generated lowered) generated run

theorem permission_source_expression_list (exprs : List Expr) (env : Core.TEnv) (func : Func) (results : List Ty)
    (tables : PermissionSourceTables env results func) {types : List Ty} {start finish : Nat}
    (source : Core.tyStructExprs env types exprs start = .ok ((), finish))
    {before after : LS} {values : List ValueId} (generated : GeneratedBuilderState before)
    (run : lowerExprs exprs (lowerEnv env.mod env.vars results) before = (values, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) before.vals.size before after := by
  exact newPermissions_lowerExprs_struct exprs source (Nat.le_refl _)
    (fun expr member type start finish typed before middle value generated lowered =>
      permission_source_expression expr env func results tables typed generated lowered) generated run

theorem permission_source_statement_list (stmts : List Stmt) (env : Core.TEnv) (func : Func) (results : List Ty)
    (scope : ScopeId) (tables : PermissionSourceTables env results func) {output : Core.TEnv} {start finish : Nat}
    (source : Core.tyStmts env scope stmts start = .ok (output, finish))
    {first : Nat} {loop : Option LoopCtx} {before after : LS} {result : Unit}
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before)
    (floor : first ≤ before.vals.size)
    (run : lowerStmts loop stmts (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  exact permission_source_statements scope stmts
    (fun stmt member env => permission_source_statement stmt env func results scope)
    tables source generated frames floor run

#print axioms permission_source_arguments
#print axioms permission_source_argument
#print axioms permission_source_expression_list
#print axioms permission_source_statement_list

#print axioms permission_source_expression
#print axioms permission_source_place
#print axioms permission_source_view
#print axioms permission_source_bound
#print axioms permission_source_expression_members
#print axioms permission_source_argument_members
#print axioms permission_source_printExpressions
#print axioms permission_source_block
#print axioms permission_source_statement_members
#print axioms permission_source_statement

end Goose.Lower.Validation
