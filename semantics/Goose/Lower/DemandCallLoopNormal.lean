import Goose.Lower.DemandWhileCallSequence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

private theorem call_loop_bind_ok {c : M α} {f : α → M β} {s s' : St} {b : β}
    (h : (c >>= f) s = .ok b s') : ∃ a middle, c s = .ok a middle ∧ f a middle = .ok b s' := by
  rw [bind_apply] at h
  cases hc : c s with
  | stop err middle => rw [hc] at h; cases h
  | ok a middle => exact ⟨a, middle, rfl, by simpa [hc] using h⟩

theorem call_single_block_normal {cfg : Cfg} {env : Env} {block : Core.Block}
    {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
    (bodyStatements : block.stmts = [.expr (.call context arguments origin) statementOrigin]) (noValue : block.value = none)
    {fuel : Nat} {state after : St} {flow : Flow}
    (done : execBlock fuel cfg env [] block state = .ok flow after) : flow = .normal .unit := by
  cases fuel with
  | zero => simp [execBlock, timeout, M.stop] at done
  | succ fuel =>
    cases block with
    | mk scope statements value =>
      simp only [Core.Block.stmts] at bodyStatements
      simp only [Core.Block.value] at noValue
      subst statements
      subst value
      rw [execBlock_pre] at done
      unfold prefixCoreBlock at done
      obtain ⟨si, middle, _, rest⟩ := call_loop_bind_ok done
      obtain ⟨_, bound, _, rest⟩ := call_loop_bind_ok rest
      obtain ⟨bodyFlow, afterBody, bodyDone, rest⟩ := call_loop_bind_ok rest
      have normal := call_expression_single_normal bodyDone
      subst bodyFlow
      simp only [valueFlow, pure_bind] at rest
      obtain ⟨_, final, _, rest⟩ := call_loop_bind_ok rest
      simp only [pure_apply, Res.ok.injEq] at rest
      exact rest.1.symm

theorem call_loop_normal {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
    (bodyStatements : body.stmts = [.expr (.call context arguments origin) statementOrigin]) (noValue : body.value = none)
    {fuel : Nat} {state after : St} {flow : Flow}
    (done : execWhile fuel cfg env condition body state = .ok flow after) : flow = .normal .unit := by
  induction fuel generalizing state after flow with
  | zero => simp [execWhile, timeout, M.stop] at done
  | succ fuel ih =>
    rw [execWhile] at done
    obtain ⟨value, middle, _, rest⟩ := call_loop_bind_ok done
    obtain ⟨choice, tested, _, rest⟩ := call_loop_bind_ok rest
    cases choice with
    | false => simpa [pure_apply] using (Res.ok.inj rest).1.symm
    | true =>
      obtain ⟨bodyFlow, bodyAfter, bodyDone, rest⟩ := call_loop_bind_ok rest
      have normal := call_single_block_normal bodyStatements noValue bodyDone
      subst bodyFlow
      exact ih rest

theorem call_loop_statement_single_normal {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {loopOrigin : OriginId} {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
    (bodyStatements : body.stmts = [.expr (.call context arguments origin) statementOrigin]) (noValue : body.value = none)
    {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env [.while condition body loopOrigin] state = .ok flow after) : flow = .normal .unit := by
  cases fuel with
  | zero => simp [execStmts, timeout, M.stop] at done
  | succ fuel =>
    cases head : execStmt fuel cfg env (.while condition body loopOrigin) state with
    | stop reason final => simp [execStmts, bind_apply, head] at done
    | ok headFlow middle =>
      cases fuel with
      | zero => simp [execStmt, timeout, M.stop] at head
      | succ fuel =>
        simp only [execStmt] at head
        have normal : headFlow = .normal .unit := call_loop_normal bodyStatements noValue head
        subst headFlow
        simp [execStmts, execStmt, bind_apply, head, pure_apply] at done
        exact done.1.symm

#print axioms call_loop_statement_single_normal

#print axioms call_loop_normal

#print axioms call_single_block_normal
end Goose.Lower
