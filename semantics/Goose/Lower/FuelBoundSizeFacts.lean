import Goose.Lower.FuelBoundSize

namespace Goose.Lower.SourceFuelSize

open Goose.Core

theorem expr_pos (expression : Expr) : 0 < expr expression := by
  cases expression <;> simp only [expr] <;> omega

theorem place_pos (owner : Place) : 0 < place owner := by
  cases owner <;> simp only [place] <;> omega

theorem view_pos (source : View) : 0 < view source := by
  cases source <;> simp only [view] <;> omega

theorem boundary_pos (bound : Bound) : 0 < boundary bound := by
  cases bound <;> simp only [boundary] <;> omega

theorem arg_pos (argument : Arg) : 0 < arg argument := by
  cases argument <;> simp only [arg] <;> omega

theorem block_pos (body : Core.Block) : 0 < block body := by
  cases body <;> simp only [block] <;> omega

theorem stmt_pos (statement : Stmt) : 0 < stmt statement := by
  cases statement <;> simp only [stmt] <;> omega

theorem stmts_pos (statements : List Stmt) : 0 < stmts statements := by
  cases statements <;> simp only [stmts] <;> omega

theorem exprs_pos (expressions : List Expr) : 0 < exprs expressions := by
  cases expressions <;> simp only [exprs] <;> omega

theorem args_pos (arguments : List Arg) : 0 < args arguments := by
  cases arguments <;> simp only [args] <;> omega

theorem printArgs_pos (arguments : List PrintArg) : 0 < printArgs arguments := by
  cases arguments with
  | nil => simp only [printArgs]; omega
  | cons argument rest => cases argument <;> simp only [printArgs] <;> omega

theorem exprs_member_lt {expression : Expr} {expressions : List Expr}
    (member : expression ∈ expressions) : expr expression < exprs expressions := by
  induction expressions with
  | nil => cases member
  | cons head tail ih =>
    simp only [exprs]
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have smaller := ih member
      omega

theorem args_member_lt {argument : Arg} {arguments : List Arg}
    (member : argument ∈ arguments) : arg argument < args arguments := by
  induction arguments with
  | nil => cases member
  | cons head tail ih =>
    simp only [args]
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have smaller := ih member
      omega

theorem stmts_member_lt {statement : Stmt} {statements : List Stmt}
    (member : statement ∈ statements) : stmt statement < stmts statements := by
  induction statements with
  | nil => cases member
  | cons head tail ih =>
    simp only [stmts]
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have smaller := ih member
      omega

theorem printArgs_expr_member_lt {expression : Expr} {arguments : List PrintArg}
    (member : PrintArg.expr expression ∈ arguments) : expr expression < printArgs arguments := by
  induction arguments with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp only [printArgs]
      omega
    · have smaller := ih member
      cases head <;> simp only [printArgs] <;> omega

theorem optionalExpr_child_lt {value : Option Expr} {expression : Expr}
    (present : value = some expression) : expr expression < optionalExpr value := by
  subst value
  simp only [optionalExpr]
  omega

theorem optionalBlock_child_lt {value : Option Core.Block} {body : Core.Block}
    (present : value = some body) : block body < optionalBlock value := by
  subst value
  simp only [optionalBlock]
  omega

theorem exprs_tail_lt (expression : Expr) (rest : List Expr) : exprs rest < exprs (expression :: rest) := by
  simp only [exprs]
  omega

theorem args_tail_lt (argument : Arg) (rest : List Arg) : args rest < args (argument :: rest) := by
  simp only [args]
  omega

theorem stmts_tail_lt (statement : Stmt) (rest : List Stmt) : stmts rest < stmts (statement :: rest) := by
  simp only [stmts]
  omega

theorem printArgs_tail_lt (argument : PrintArg) (rest : List PrintArg) :
    printArgs rest < printArgs (argument :: rest) := by
  cases argument <;> simp only [printArgs] <;> omega

theorem deref_slice_reference_child_lt (index : VarId) :
    expr (.read (.var index)) < place (.deref (.read (.var index))) := by
  simp only [expr, place]
  omega

theorem deref_slice_reference_size (index : VarId) :
    place (.deref (.read (.var index))) = 3 := by
  simp only [expr, place]

end Goose.Lower.SourceFuelSize
