import Goose.Core.Sound.StepExpr
import Goose.Core.Sound.StepPlace
import Goose.Core.Sound.StepStmt
import Goose.Core.Sound.StepStmt2
import Goose.Core.Sound.StepBlock2
import Goose.Core.Sound.StepLoop
import Goose.Core.Sound.StepCall3
import Goose.Core.Sound.Module
import Goose.Core.Sound.ShrinkBridge

/-!
The induction on fuel: every evaluation function meets its statement at every
fuel, for a module whose items passed the validator's stages.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}

theorem step_expr (hm : ModOk m) (ih : Specs m prof n) : ExprSpec m prof (n + 1) := by
  intro W tenv penv env s e tn tn' ty rst rst' rho hp hF ht hr hE
  cases e <;> first
    | exact step_expr_a ih _ _ _ _ _ _ _ _ _ _ _ _ trivial hp hF ht hr hE
    | exact step_expr_b ih _ _ _ _ _ _ _ _ _ _ _ _ trivial hp hF ht hr hE
    | exact step_expr_call hm ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp hF ht hr hE

theorem step_stmt (ih : Specs m prof n) : StmtSpec m prof (n + 1) := by
  intro W tenv tenv' penv env s sc st tn tn' rst rst' lo hp hF hsc hT hlo ht hr hE
  cases st <;> first
    | exact step_stmt_a ih _ _ _ _ _ _ _ _ _ _ _ _ _ trivial hp hF hsc hT hlo ht hr hE
    | exact step_stmt_b ih _ _ _ _ _ _ _ _ _ _ _ _ _ trivial hp hF hsc hT hlo ht hr hE

theorem specs_zero : Specs m prof 0 where
  expr := by unfold ExprSpec; intros; simp only [evalExpr, sat_timeout]
  blockValue := by unfold BlockValueSpec; intros; unfold blockValue; trivial
  arg := by unfold ArgSpec; intros; simp only [evalArg, sat_timeout]
  bound := by unfold BoundSpec; intros; simp only [evalBound, sat_timeout]
  place := by unfold PlaceSpec; intros; simp only [evalPlace, sat_timeout]
  view := by unfold ViewSpec; intros; simp only [evalView, sat_timeout]
  call := by unfold CallSpec; intros; simp only [enterCall, sat_timeout]
  block := by unfold BlockSpec; intros; simp only [execBlock, sat_timeout]
  stmts := by unfold StmtsSpec; intros; simp only [execStmts, sat_timeout]
  stmt := by unfold StmtSpec; intros; simp only [execStmt, sat_timeout]
  printArg := by unfold PrintArgSpec; intros; simp only [execPrintArg, sat_timeout]
  while_ := by unfold WhileSpec; intros; simp only [execWhile, sat_timeout]
  range := by unfold RangeSpec; intros; simp only [execRange, sat_timeout]
  each := by unfold EachSpec; intros; unfold execEach; trivial

theorem specs_succ (hm : ModOk m) (ih : Specs m prof n) : Specs m prof (n + 1) where
  expr := step_expr hm ih
  blockValue := step_blockValue ih
  arg := step_arg ih
  bound := step_bound ih
  place := step_place hm ih
  view := step_view ih
  call := step_call hm ih
  block := step_block ih
  stmts := step_stmts ih
  stmt := step_stmt ih
  printArg := step_printArg ih
  while_ := step_while ih
  range := step_range ih
  each := step_each ih

/-- Every evaluation function, at every fuel, on code of a module whose items
the validator accepted: it does not fault, and it keeps the frame, hence the
store invariant, true. -/
theorem specs_all (hm : ModOk m) (prof : NumProfile) : ∀ n, Specs m prof n
  | 0 => specs_zero
  | n + 1 => specs_succ hm (specs_all hm prof n)

end Goose.Core.Sound
