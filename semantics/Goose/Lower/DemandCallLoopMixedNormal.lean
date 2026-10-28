import Goose.Lower.DemandCallLoopNormal
import Goose.Lower.DemandCallLoopMixedSequence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem scalar_call_block_normal {cfg : Cfg} {env : Env} {block : Core.Block}
    {other : Env} (fragment : ReachableScalarCallStatements cfg other block.stmts) (noValue : block.value = none)
    {fuel : Nat} {state after : St} {flow : Flow}
    (done : execBlock fuel cfg env [] block state = .ok flow after) : flow = .normal .unit := by
  apply call_block_normal_of_stmts ?_ noValue done
  intro innerEnv fuel state after flow result
  exact fragment.normal_any_env result

theorem scalar_call_loop_normal {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {other : Env} (fragment : ReachableScalarCallStatements cfg other body.stmts) (noValue : body.value = none)
    {fuel : Nat} {state after : St} {flow : Flow}
    (done : execWhile fuel cfg env condition body state = .ok flow after) : flow = .normal .unit := by
  apply call_loop_normal_of_stmts ?_ noValue done
  intro innerEnv fuel state after flow result
  exact fragment.normal_any_env result

theorem scalar_call_loop_statement_normal {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {loopOrigin : OriginId} {other : Env} (fragment : ReachableScalarCallStatements cfg other body.stmts) (noValue : body.value = none)
    {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env [.while condition body loopOrigin] state = .ok flow after) : flow = .normal .unit := by
  apply call_loop_statement_normal_of_stmts ?_ noValue done
  intro innerEnv fuel state after flow result
  exact fragment.normal_any_env result

#print axioms scalar_call_block_normal
#print axioms scalar_call_loop_normal
#print axioms scalar_call_loop_statement_normal
end Goose.Lower
