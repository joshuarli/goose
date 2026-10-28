import Goose.Lower.DemandCallReachableMixedRecursive
import Goose.Lower.DemandCallLoopBody

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

private theorem statement_ok_of_member {statements : List Stmt} (valid : stmtsOk statements = true)
    {statement : Stmt} (member : statement ∈ statements) : stmtOk statement = true := by
  induction statements with
  | nil => simp at member
  | cons head tail ih =>
    simp only [stmtsOk, Bool.and_eq_true] at valid
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact valid.1
    · exact ih valid.2 member

private theorem ReachableMixedCallStatements.members {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : ReachableMixedCallStatements cfg env statements) : ∀ statement ∈ statements, stmtOk statement = true ∨
      ∃ context arguments origin statementOrigin, statement = .expr (.call context arguments origin) statementOrigin := by
  induction form with
  | mixed fragment =>
    intro statement member
    exact Or.inl (statement_ok_of_member fragment.fragment member)
  | @call earlier later earlierForm context arguments origin statementOrigin ctx impl contextAt implAt depth fragment expression exprForm hasValue shrink argumentsForm stoppedArgumentsForm tail ih =>
    intro statement member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with member | rfl | member
    · exact Or.inl (statement_ok_of_member earlierForm.fragment member)
    · exact Or.inr ⟨context, arguments, origin, statementOrigin, rfl⟩
    · exact ih statement member

private theorem call_mixed_members_normal {cfg : Cfg} {env : Env} {statements : List Stmt}
    (members : ∀ statement ∈ statements, stmtOk statement = true ∨
      ∃ context arguments origin statementOrigin, statement = .expr (.call context arguments origin) statementOrigin)
    {fuel : Nat} {state after : St} {flow : Flow}
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
      simp only [execStmts, bind_apply] at done
      cases evaluated : execStmt fuel cfg env head state with
      | stop stop final => simp only [evaluated] at done; cases done
      | ok headFlow middle =>
        have normal : headFlow = .normal .unit := by
          rcases members head (by simp) with valid | ⟨context, arguments, origin, statementOrigin, rfl⟩
          · exact execStmt_fragment_normal fuel cfg env head valid state middle headFlow evaluated
          · cases fuel with
            | zero => simp [execStmt, timeout, M.stop] at evaluated
            | succ fuel =>
              simp only [execStmt, Functor.map, bind_apply] at evaluated
              cases value : evalExpr fuel cfg env (.call context arguments origin) state with
              | stop reason final => simp only [value] at evaluated; cases evaluated
              | ok result final =>
                simp only [value, pure_apply, Res.ok.injEq] at evaluated
                exact evaluated.1.symm
        subst headFlow
        simp only [evaluated] at done
        exact ih (by intro statement member; exact members statement (by simp [member])) done

theorem ReachableMixedCallStatements.normal {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : ReachableMixedCallStatements cfg env statements) {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env statements state = .ok flow after) : flow = .normal .unit :=
  call_mixed_members_normal form.members done

theorem ReachableMixedCallStatements.normal_any_env {cfg : Cfg} {env other : Env} {statements : List Stmt}
    (form : ReachableMixedCallStatements cfg env statements) {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg other statements state = .ok flow after) : flow = .normal .unit :=
  call_mixed_members_normal form.members done

#print axioms ReachableMixedCallStatements.normal_any_env

#print axioms ReachableMixedCallStatements.normal
end Goose.Lower
