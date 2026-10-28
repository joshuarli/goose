import Goose.Lower.DemandCallScalarLiteral

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem CallScalarLiteral.block_value {cfg : Cfg} {env : Env} {pre : List (VarId × Val)} {block : Core.Block} {state after : St}
    {expression : Expr} {expected : Val} {operation : Op}
    (literal : CallScalarLiteral expression expected operation) (hasValue : block.value = some expression)
    (fragment : WhileMixedStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts)
    {fuel : Nat} {value : Val} (done : execBlock fuel cfg env pre block state = .ok (.normal value) after) :
    value = expected := by
  cases fuel with
  | zero => simp [execBlock, timeout, M.stop] at done
  | succ fuel =>
    cases block with
    | mk scope stmts tail =>
      simp only [Core.Block.value] at hasValue
      subst tail
      cases stmtsDone : execStmts fuel cfg { env with scopes := (scope, state.nextScope) :: env.scopes } stmts
          { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } with
      | stop reason final => simp [execBlock, freshScope, bindAll_eq, bind_apply, stmtsDone] at done
      | ok flow middle =>
        have normal := fragment.normal stmtsDone
        subst flow
        cases fuel with
        | zero => cases literal <;> simp [execBlock, freshScope, bindAll_eq, bind_apply, stmtsDone, evalExpr, timeout, M.stop] at done
        | succ fuel =>
          cases literal <;> simp [execBlock, freshScope, bindAll_eq, bind_apply, stmtsDone, evalExpr, pure_apply] at done <;>
            cases release : releaseScope env scope state.nextScope middle <;> simp_all [Functor.map, M.bind', M.pure']

#print axioms CallScalarLiteral.block_value
end Goose.Lower
