import Goose.Lower.Validation.SourceValueTypeShapesSourceChecks
import Goose.Lower.Validation.ExpressionTypingAggregateOps
import Goose.Lower.Validation.ExpressionTypingSliceOps
import Goose.Lower.Validation.ViewTyping
import Goose.Lower.Validation.SourceStatementTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

mutual

theorem shape_tyExpr_annotations (expr : Expr) (env : Core.TEnv) {type : Ty} {start finish : Nat} :
    Core.tyExpr env expr start = .ok (type, finish) → Core.checkStructTables env.mod = .ok () →
    ShapeExprAnnotations env.mod expr := by
  cases expr with
  | lit integer value | bool value => intros; trivial
  | read place =>
    intro source tables
    obtain ⟨_, _, child, _⟩ := tyExpr_read_place source
    exact shape_tyPlace_annotations place env child tables
  | ref mu place =>
    intro source tables
    obtain ⟨_, _, child, _, _⟩ := tyExpr_ref_place source
    exact shape_tyPlace_annotations place env child tables
  | slice mu view low high origin =>
    intro source tables
    obtain ⟨_, _, _, _, _, _, viewSource, lowSource, highSource, _⟩ := tyExpr_slice_children source
    exact ⟨shape_tyView_annotations view env viewSource tables,
      shape_tyBound_annotations low env lowSource tables, shape_tyBound_annotations high env highSource tables⟩
  | len view =>
    intro source tables
    obtain ⟨_, _, child, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact shape_tyView_annotations view env child tables
  | un op expr origin =>
    intro source tables
    obtain ⟨_, _, _, child, _, _⟩ := tyExpr_un_child source
    exact shape_tyExpr_annotations expr env child tables
  | bin op left right origin =>
    intro source tables
    obtain ⟨_, _, _, _, _, leftSource, rightSource, _⟩ := tyExpr_bin_children source
    exact ⟨shape_tyExpr_annotations left env leftSource tables, shape_tyExpr_annotations right env rightSource tables⟩
  | cmp op left right =>
    intro source tables
    obtain ⟨_, _, _, _, leftSource, rightSource, _, _⟩ := tyExpr_comparison_children source
    exact ⟨shape_tyExpr_annotations left env leftSource tables, shape_tyExpr_annotations right env rightSource tables⟩
  | and left right | or left right =>
    intro source tables
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, rightSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact ⟨shape_tyExpr_annotations left env leftSource tables, shape_tyExpr_annotations right env rightSource tables⟩
  | not expr =>
    intro source tables
    obtain ⟨_, child, _⟩ := tyExpr_not_child source
    exact shape_tyExpr_annotations expr env child tables
  | conv kind target expr origin =>
    intro source tables
    obtain ⟨_, _, _, _, child, _, _, _⟩ := tyExpr_conversion_child source
    exact shape_tyExpr_annotations expr env child tables
  | call context args origin =>
    intro source tables
    obtain ⟨_, _, _, _, _, _, _, length, children, _⟩ := tyExpr_call_tables source
    exact shape_tyArgs_annotations args env length children tables
  | push owner expr origin =>
    intro source tables
    obtain ⟨_, _, _, _, _, _, ownerSource, _, child, _⟩ := tyExpr_push_children source
    exact ⟨shape_tyPlace_annotations owner env ownerSource tables, shape_tyExpr_annotations expr env child tables⟩
  | pop owner origin =>
    intro source tables
    obtain ⟨_, _, _, ownerSource, _⟩ := tyExpr_pop_owner source
    exact shape_tyPlace_annotations owner env ownerSource tables
  | ifE condition yes no =>
    intro source tables
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, conditionSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, yesSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, noSource, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact ⟨shape_tyExpr_annotations condition env conditionSource tables,
      shape_tyBlock_annotations yes (Core.exprEnv env) yesSource tables,
      shape_tyBlock_annotations no (Core.exprEnv env) noSource tables⟩
  | blockE body =>
    intro source tables
    exact shape_tyBlock_annotations body (Core.exprEnv env) source tables
  | arrLit annotation exprs =>
    intro source tables
    obtain ⟨_, _, _, _, _, _, children⟩ := tyExpr_arrayLiteral_children source
    exact ⟨shape_tyExpr_arrLit_storable source,
      shape_tyExprs_annotations exprs env (tyExprsAs_structExprs children) tables⟩
  | structLit annotation exprs =>
    intro source tables
    obtain ⟨_, _, _, _, _, _, children⟩ := tyExpr_structLiteral_children source
    exact ⟨shape_tyExpr_structLit_storable source, shape_tyExprs_annotations exprs env children tables⟩
  | fill annotation expr =>
    intro source tables
    obtain ⟨_, _, _, _, _, _, child⟩ := tyExpr_fill_child source
    exact ⟨shape_tyExpr_fill_storable source, shape_tyExpr_annotations expr env child tables⟩
termination_by sizeOf expr

theorem shape_tyExprs_annotations (exprs : List Expr) (env : Core.TEnv)
    {types : List Ty} {start finish : Nat} :
    Core.tyStructExprs env types exprs start = .ok ((), finish) → Core.checkStructTables env.mod = .ok () →
    ShapeExprsAnnotations env.mod exprs := by
  cases exprs with
  | nil => intros; trivial
  | cons expr rest =>
    intro source tables
    cases types with
    | nil => exact (rej_ok _ _ _ _).mp source |>.elim
    | cons type types =>
      simp only [Core.tyStructExprs] at source
      obtain ⟨childType, _, child, source⟩ := (st_bind_ok _ _ _ _).mp source
      by_cases same : (childType == type) = true
      · simp only [same, ite_true] at source
        exact ⟨shape_tyExpr_annotations expr env child tables, shape_tyExprs_annotations rest env source tables⟩
      · simp [same, chk] at source
termination_by sizeOf exprs

theorem shape_tyArgs_annotations (args : List Arg) (env : Core.TEnv)
    {callee : Core.Impl} {params : List Param} {start finish : Nat} : params.length = args.length →
    Core.tyArgs env callee params args start = .ok ((), finish) → Core.checkStructTables env.mod = .ok () →
    ShapeArgsAnnotations env.mod args := by
  cases args with
  | nil => intros; trivial
  | cons arg rest =>
    cases arg with
    | byVal expr =>
      intro length source tables
      cases params with
      | nil => simp at length
      | cons param params =>
        obtain ⟨_, _, _, _, _, _, child, _, remaining⟩ := tyArgs_byVal_head source
        exact ⟨shape_tyExpr_annotations expr env child tables,
          shape_tyArgs_annotations rest env (by simpa using length) remaining tables⟩
    | byRef mu place =>
      intro length source tables
      cases params with
      | nil => simp at length
      | cons param params =>
        obtain ⟨_, _, _, _, _, child, _, _, remaining⟩ := tyArgs_byRef_head source
        exact ⟨shape_tyPlace_annotations place env child tables,
          shape_tyArgs_annotations rest env (by simpa using length) remaining tables⟩
termination_by sizeOf args

theorem shape_tyPlace_annotations (place : Place) (env : Core.TEnv)
    {info : PlaceInfo} {start finish : Nat} :
    Core.tyPlace env place start = .ok (info, finish) → Core.checkStructTables env.mod = .ok () →
    ShapePlaceAnnotations env.mod place := by
  cases place with
  | var index | global index => intros; trivial
  | field owner index =>
    intro source tables
    obtain ⟨_, _, child, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact shape_tyPlace_annotations owner env child tables
  | deref expr =>
    intro source tables
    cases special : Core.sliceRefTy env expr with
    | none =>
      obtain ⟨_, _, child⟩ := tyPlace_deref_child special source
      exact shape_tyExpr_annotations expr env child tables
    | some type =>
      cases expr with
      | read place =>
        cases place <;> simp only [Core.sliceRefTy] at special
        all_goals try contradiction
        trivial
      | _ => simp [Core.sliceRefTy] at special
  | elem view index origin =>
    intro source tables
    obtain ⟨_, _, _, _, _, viewSource, indexSource⟩ := tyPlace_elem_children source
    exact ⟨shape_tyView_annotations view env viewSource tables, shape_tyExpr_annotations index env indexSource tables⟩
termination_by sizeOf place

theorem shape_tyView_annotations (view : View) (env : Core.TEnv)
    {info : Ty × Bool} {start finish : Nat} :
    Core.tyView env view start = .ok (info, finish) → Core.checkStructTables env.mod = .ok () →
    ShapeViewAnnotations env.mod view := by
  cases view with
  | of place =>
    intro source tables
    obtain ⟨_, _, child, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact shape_tyPlace_annotations place env child tables
  | val expr =>
    intro source tables
    obtain ⟨_, _, child, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact shape_tyExpr_annotations expr env child tables
termination_by sizeOf view

theorem shape_tyBound_annotations (bound : Bound) (env : Core.TEnv) {start finish : Nat} :
    Core.tyBound env bound start = .ok ((), finish) → Core.checkStructTables env.mod = .ok () →
    ShapeBoundAnnotations env.mod bound := by
  cases bound with
  | omitted => intros; trivial
  | expr expr | fromEnd expr =>
    intro source tables
    obtain ⟨_, _, child⟩ := tyBound_child source
    exact shape_tyExpr_annotations expr env child tables
termination_by sizeOf bound

theorem shape_tyBlock_annotations (body : Core.Block) (env : Core.TEnv)
    {pre : List (VarId × Ty)} {type : Ty} {start finish : Nat} :
    Core.tyBlock env pre body start = .ok (type, finish) → Core.checkStructTables env.mod = .ok () →
    ShapeBlockAnnotations env.mod body := by
  cases body with
  | mk scope stmts value =>
    cases value with
    | none =>
      intro source tables
      obtain ⟨_, initializedEnv, finalEnv, _, _, declared, statements, valueSource⟩ := tyBlock_checked_children source
      have same := (declarePre_tables pre declared).1
      have annotations := shape_tyStmts_annotations stmts initializedEnv statements (same.symm ▸ tables)
      exact ⟨same ▸ annotations, trivial⟩
    | some expr =>
      intro source tables
      obtain ⟨_, initializedEnv, finalEnv, _, _, declared, statements, valueSource⟩ := tyBlock_checked_children source
      have initialSame := (declarePre_tables pre declared).1
      have finalSame := (tyStmts_tables stmts statements).1.trans initialSame
      have statementsSyntax := shape_tyStmts_annotations stmts initializedEnv statements (initialSame.symm ▸ tables)
      have valueSyntax := shape_tyExpr_annotations expr finalEnv valueSource (finalSame.symm ▸ tables)
      exact ⟨initialSame ▸ statementsSyntax, finalSame ▸ valueSyntax⟩
termination_by sizeOf body

theorem shape_tyStmts_annotations (stmts : List Stmt) (env : Core.TEnv)
    {output : Core.TEnv} {scope start finish : Nat} :
    Core.tyStmts env scope stmts start = .ok (output, finish) → Core.checkStructTables env.mod = .ok () →
    ShapeStmtsAnnotations env.mod stmts := by
  cases stmts with
  | nil => intros; trivial
  | cons stmt rest =>
    intro source tables
    obtain ⟨middle, _, first, remaining⟩ := tyStmts_cons_children source
    have same := (tyStmt_tables stmt first).1
    have tail := shape_tyStmts_annotations rest middle remaining (same.symm ▸ tables)
    exact ⟨shape_tyStmt_annotations stmt env first tables, same ▸ tail⟩
termination_by sizeOf stmts

theorem shape_tyPrint_annotations (args : List PrintArg) (env : Core.TEnv) {start finish : Nat} :
    Core.tyPrintArgs env args start = .ok ((), finish) → Core.checkStructTables env.mod = .ok () →
    ShapePrintAnnotations env.mod args := by
  cases args with
  | nil => intros; trivial
  | cons arg rest =>
    cases arg with
    | text text =>
      intro source tables
      exact shape_tyPrint_annotations rest env source tables
    | expr expr =>
      intro source tables
      obtain ⟨type, _, child, tail⟩ := (st_bind_ok _ _ _ _).mp source
      cases type <;> try exact (rej_ok _ _ _ _).mp tail |>.elim
      all_goals exact ⟨shape_tyExpr_annotations expr env child tables, shape_tyPrint_annotations rest env tail tables⟩
termination_by sizeOf args

theorem shape_tyStmt_annotations (stmt : Stmt) (env : Core.TEnv)
    {output : Core.TEnv} {scope start finish : Nat} :
    Core.tyStmt env scope stmt start = .ok (output, finish) → Core.checkStructTables env.mod = .ok () →
    ShapeStmtAnnotations env.mod stmt := by
  cases stmt with
  | letS index expr origin =>
    intro source tables
    obtain ⟨_, _, _, _, child, _, _⟩ := tyStmt_let_children source
    exact shape_tyExpr_annotations expr env child tables
  | assign place expr origin =>
    intro source tables
    obtain ⟨_, _, placeSource, child, _⟩ := tyStmt_assign_children source
    exact ⟨shape_tyPlace_annotations place env placeSource tables, shape_tyExpr_annotations expr env child tables⟩
  | assignOp op place expr origin =>
    intro source tables
    obtain ⟨_, _, _, placeSource, _, child, _⟩ := tyStmt_assignOp_children source
    exact ⟨shape_tyPlace_annotations place env placeSource tables, shape_tyExpr_annotations expr env child tables⟩
  | rebind index expr origin =>
    intro source tables
    obtain ⟨_, _, _, _, _, _, child, _⟩ := tyStmt_rebind_children source
    exact shape_tyExpr_annotations expr env child tables
  | expr expr origin =>
    intro source tables
    obtain ⟨_, child, _⟩ := tyStmt_expr_children source
    exact shape_tyExpr_annotations expr env child tables
  | append place view origin =>
    intro source tables
    obtain ⟨_, _, _, _, placeSource, _, viewSource, _⟩ := tyStmt_append_children source
    exact ⟨shape_tyPlace_annotations place env placeSource tables, shape_tyView_annotations view env viewSource tables⟩
  | popN place count origin =>
    intro source tables
    obtain ⟨_, _, _, _, placeSource, _, child, _⟩ := tyStmt_popN_children source
    exact ⟨shape_tyPlace_annotations place env placeSource tables, shape_tyExpr_annotations count env child tables⟩
  | resize place size fill origin =>
    cases fill with
    | none =>
      intro source tables
      obtain ⟨_, _, _, _, _, placeSource, _, child, _, _⟩ := tyStmt_resize_children source
      exact ⟨shape_tyPlace_annotations place env placeSource tables, shape_tyExpr_annotations size env child tables, trivial⟩
    | some fill =>
      intro source tables
      obtain ⟨_, _, _, _, _, placeSource, _, child, fillSource, _⟩ := tyStmt_resize_children source
      exact ⟨shape_tyPlace_annotations place env placeSource tables, shape_tyExpr_annotations size env child tables,
        shape_tyExpr_annotations fill env fillSource tables⟩
  | clear place origin =>
    intro source tables
    obtain ⟨_, _, placeSource, _⟩ := tyStmt_clear_children source
    exact shape_tyPlace_annotations place env placeSource tables
  | assignWhole place expr origin =>
    intro source tables
    obtain ⟨_, _, _, placeSource, _, child, _⟩ := tyStmt_assignWhole_children source
    exact ⟨shape_tyPlace_annotations place env placeSource tables, shape_tyExpr_annotations expr env child tables⟩
  | ifS condition yes no origin =>
    cases no with
    | none =>
      intro source tables
      obtain ⟨_, _, _, conditionSource, yesSource, _, _⟩ := tyStmt_if_children source
      exact ⟨shape_tyExpr_annotations condition env conditionSource tables,
        shape_tyBlock_annotations yes env yesSource tables, trivial⟩
    | some no =>
      intro source tables
      obtain ⟨_, _, _, conditionSource, yesSource, noSource, _⟩ := tyStmt_if_children source
      obtain ⟨_, noSource⟩ := noSource
      exact ⟨shape_tyExpr_annotations condition env conditionSource tables,
        shape_tyBlock_annotations yes env yesSource tables, shape_tyBlock_annotations no env noSource tables⟩
  | «while» condition body origin =>
    intro source tables
    obtain ⟨_, _, conditionSource, bodySource, _⟩ := tyStmt_while_children source
    exact ⟨shape_tyExpr_annotations condition env conditionSource tables,
      shape_tyBlock_annotations body {env with loops := env.loops + 1} bodySource tables⟩
  | forRange index low high body origin =>
    intro source tables
    obtain ⟨_, _, _, _, _, _, _, lowSource, highSource, _, bodySource, _⟩ := tyStmt_forRange_children source
    exact ⟨shape_tyExpr_annotations low env lowSource tables, shape_tyExpr_annotations high env highSource tables,
      shape_tyBlock_annotations body {env with loops := env.loops + 1, visible := index :: env.visible} bodySource tables⟩
  | forEach index optional view byRef body origin =>
    cases optional with
    | none =>
      intro source tables
      obtain ⟨_, _, _, _, _, _, _, _, _, viewSource, _, bodySource, _⟩ := tyStmt_forEach_children source
      exact ⟨shape_tyView_annotations view env viewSource tables, shape_tyBlock_annotations body {env with loops := env.loops + 1, visible := index :: env.visible} bodySource tables⟩
    | some optional =>
      intro source tables
      obtain ⟨_, _, _, _, _, _, _, _, _, viewSource, _, bodySource, _⟩ := tyStmt_forEach_children source
      exact ⟨shape_tyView_annotations view env viewSource tables, shape_tyBlock_annotations body {env with loops := env.loops + 1, visible := index :: optional :: env.visible} bodySource tables⟩
  | ret expr origin =>
    cases expr with
    | none => intros; trivial
    | some expr =>
      intro source tables
      obtain ⟨_, _, _, _, _, _, child, _⟩ := tyStmt_return_children source
      exact shape_tyExpr_annotations expr env child tables
  | print args origin =>
    intro source tables
    exact shape_tyPrint_annotations args env (tyStmt_print_children source).1 tables
  | assertS expr origin =>
    intro source tables
    exact shape_tyExpr_annotations expr env (tyStmt_assert_children source).1 tables
  | exit expr origin =>
    intro source tables
    obtain ⟨_, child, _⟩ := tyStmt_exit_children source
    exact shape_tyExpr_annotations expr env child tables
  | brk origin | cont origin | abort kind origin => intros; trivial
termination_by sizeOf stmt

end

end Goose.Lower.Validation
