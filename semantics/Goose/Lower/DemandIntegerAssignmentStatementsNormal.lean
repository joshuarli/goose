import Goose.Lower.DemandIntegerAssignmentStatementAgreement
import Goose.Lower.DemandStoppedBlockStatements

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem IntegerAssignmentStatements.normal {statements : List Stmt} (fragment : IntegerAssignmentStatements statements)
    {cfg : Cfg} {env : Env} {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env statements state = .ok flow after) : flow = .normal .unit := by
  induction fragment generalizing fuel state after with
  | nil =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, pure_apply, Res.ok.injEq] at done
      exact done.1.symm
  | clear global origin tail ih =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, bind_apply] at done
      cases head : execStmt fuel cfg env (.clear (.global global) origin) state with
      | stop stop final => simp only [head] at done; cases done
      | ok headFlow middle =>
        obtain ⟨rfl, _⟩ := global_clear_source head
        simp only [head] at done
        exact ih done
  | @expression expression origin form rest tail ih =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, bind_apply] at done
      cases head : execStmt fuel cfg env (.expr expression origin) state with
      | stop stop final => simp only [head] at done; cases done
      | ok headFlow middle =>
        have normal : headFlow = .normal .unit := by
          cases fuel with
          | zero => simp [execStmt, timeout, M.stop] at head
          | succ fuel =>
            simp only [execStmt, bind_apply] at head
            cases evaluated : evalExpr fuel cfg env expression state with
            | stop stop final => simp only [evaluated] at head; cases head
            | ok value final => simp only [evaluated, pure_apply, Res.ok.injEq] at head; exact head.1.symm
        subst headFlow
        simp only [head] at done
        exact ih done

  | @assignment place form expression value origin rest tail ih =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, bind_apply] at done
      cases head : execStmt fuel cfg env (.assign place expression origin) state with
      | stop stop final => simp only [head] at done; cases done
      | ok headFlow middle =>
        have normal : headFlow = .normal .unit := by
          cases fuel with
          | zero => simp [execStmt, timeout, M.stop] at head
          | succ fuel =>
            simp only [execStmt, bind_apply] at head
            cases placed : evalPlace fuel cfg env place state with
            | stop stop final => simp only [placed] at head; cases head
            | ok location addressed =>
              simp only [placed] at head
              cases evaluated : evalExpr fuel cfg env expression addressed with
              | stop stop final => simp only [evaluated] at head; cases head
              | ok value valued =>
                simp only [evaluated] at head
                cases written : writeLoc location value valued with
                | stop stop final => simp only [written] at head; cases head
                | ok writtenUnit final =>
                  cases writtenUnit
                  simp only [written, pure_apply, Res.ok.injEq] at head
                  exact head.1.symm
        subst headFlow
        simp only [head] at done
        exact ih done

#print axioms IntegerAssignmentStatements.normal

end Goose.Lower
