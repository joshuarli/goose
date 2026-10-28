import Goose.Lower.DemandIfMixedStatements
import Goose.Lower.Normal

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem ScalarPrefixExpression.fragment {expression : Expr} (form : ScalarPrefixExpression expression) : exprOk expression = true := by
  induction form <;> simp_all [exprOk, placeOk]

theorem ControlPrefixExpression.fragment {expression : Expr} (form : ControlPrefixExpression expression) : exprOk expression = true := by
  induction form <;> simp_all [exprOk, ScalarPrefixExpression.fragment]

theorem ScalarReadPlace.fragment {place : Place} (form : ScalarReadPlace place) : placeOk place = true := by
  cases form <;> rfl

theorem ScalarAssignmentStatements.fragment {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : ScalarAssignmentStatements cfg env statements) : stmtsOk statements = true := by
  induction form <;> simp_all [stmtsOk, stmtOk, placeOk, viewOk, exprOk, ScalarReadPlace.fragment,
    ControlPrefixExpression.fragment, ScalarControlExpression.control]

theorem stmtsOk_append {left right : List Stmt} (leftOk : stmtsOk left = true) (rightOk : stmtsOk right = true) :
    stmtsOk (left ++ right) = true := by
  induction left with
  | nil => exact rightOk
  | cons head tail ih =>
    simp only [List.cons_append, stmtsOk, Bool.and_eq_true] at leftOk ⊢
    exact ⟨leftOk.1, ih leftOk.2⟩

theorem IfMixedStatements.fragment {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : IfMixedStatements cfg env statements) : stmtsOk statements = true := by
  induction form with
  | nil => rfl
  | scalar fragment tail ih => exact stmtsOk_append fragment.fragment ih
  | conditional condition yes origin branch noValue tail ih =>
    have valid := (branch St.initial).fragment
    cases yes with
    | mk scope statements value =>
      simp only [Core.Block.value] at noValue
      subst value
      simp only [Core.Block.stmts] at valid
      simp [stmtsOk, stmtOk, blockOk, condition.fragment, valid, ih]
  | conditionalElse condition yes no origin yesBranch noBranch yesNoValue noNoValue tail ih =>
    have yesValid := (yesBranch St.initial).fragment
    have noValid := (noBranch St.initial).fragment
    cases yes with
    | mk yesScope yesStatements yesValue =>
      cases no with
      | mk noScope noStatements noValue =>
        simp only [Core.Block.value] at yesNoValue noNoValue
        subst yesValue
        subst noValue
        simp only [Core.Block.stmts] at yesValid noValid
        simp [stmtsOk, stmtOk, blockOk, condition.fragment, yesValid, noValid, ih]

theorem stmts_fragment_normal {cfg : Cfg} {env : Env} {statements : List Stmt}
    (valid : stmtsOk statements = true) {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env statements state = .ok flow after) : flow = .normal .unit := by
  induction statements generalizing fuel state after flow with
  | nil =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, pure_apply, Res.ok.injEq] at done
      exact done.1.symm
  | cons head tail ih =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [stmtsOk, Bool.and_eq_true] at valid
      simp only [execStmts, bind_apply] at done
      cases evaluated : execStmt fuel cfg env head state with
      | stop stop final => simp only [evaluated] at done; cases done
      | ok headFlow middle =>
        have normal := execStmt_fragment_normal fuel cfg env head valid.1 state middle headFlow evaluated
        subst headFlow
        simp only [evaluated] at done
        exact ih valid.2 done

theorem IfMixedStatements.normal {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : IfMixedStatements cfg env statements) {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env statements state = .ok flow after) : flow = .normal .unit :=
  stmts_fragment_normal form.fragment done

#print axioms IfMixedStatements.normal
end Goose.Lower
