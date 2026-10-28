import Goose.Lower.DemandIfRecursiveBlock

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive WhileIterations (cfg : Cfg) (env : Env) (condition : Expr) (body : Core.Block) : Nat → St → St → Prop
  | zero (state : St) : WhileIterations cfg env condition body 0 state state
  | next {count : Nat} {state afterCondition afterBody after : St} {conditionFuel bodyFuel : Nat} {flow : Flow}
      (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) afterCondition)
      (bodyDone : execBlock bodyFuel cfg env [] body afterCondition = .ok flow afterBody)
      (reentry : (∃ value, flow = .normal value) ∨ flow = .cont)
      (rest : WhileIterations cfg env condition body count afterBody after) :
      WhileIterations cfg env condition body (count + 1) state after

theorem accepted_while_iterations {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state after : St} (source : StmtSource cfg env (.while condition body origin) state)
    {count : Nat} (iterations : WhileIterations cfg env condition body count state after) :
    ∃ next : StmtSource cfg env (.while condition body origin) after,
      next.typingEnv = source.typingEnv ∧ next.rootsEnv = source.rootsEnv ∧ next.world = source.world ∧
      next.observation = source.observation ∧ next.plans = source.plans ∧ next.path = source.path ∧ HEq next.context source.context := by
  induction iterations with
  | zero => exact ⟨source, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩
  | @next count state afterCondition afterBody after conditionFuel bodyFuel flow conditionDone bodyDone reentry rest ih =>
    obtain ⟨middle, typing, roots, world, observation, plans, path, context⟩ :=
      source.whileAfterBodyCanonical conditionFuel bodyFuel flow conditionDone bodyDone reentry
    obtain ⟨next, nextTyping, nextRoots, nextWorld, nextObservation, nextPlans, nextPath, nextContext⟩ := ih middle
    exact ⟨next, nextTyping.trans typing, nextRoots.trans roots, nextWorld.trans world, nextObservation.trans observation,
      nextPlans.trans plans, nextPath.trans path, nextContext.trans context⟩

theorem while_iteration_reentry {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {fuel : Nat} {state afterCondition afterBody : St} {flow : Flow}
    (conditionDone : evalExpr fuel cfg env condition state = .ok (.bool true) afterCondition)
    (bodyDone : execBlock fuel cfg env [] body afterCondition = .ok flow afterBody)
    (reentry : (∃ value, flow = .normal value) ∨ flow = .cont) :
    execWhile (fuel + 1) cfg env condition body state = execWhile fuel cfg env condition body afterBody := by
  rcases reentry with ⟨value, rfl⟩ | rfl <;>
    simp only [execWhile, bind_apply, conditionDone, expectBool, pure_apply, ite_true, bodyDone]

theorem while_condition_stop {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {fuel : Nat} {state after : St} {stop : Stop}
    (stopped : evalExpr fuel cfg env condition state = .stop stop after) :
    execWhile (fuel + 1) cfg env condition body state = .stop stop after := by
  simp only [execWhile, bind_apply, stopped]

theorem while_body_stop {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {fuel : Nat} {state afterCondition after : St} {stop : Stop}
    (conditionDone : evalExpr fuel cfg env condition state = .ok (.bool true) afterCondition)
    (stopped : execBlock fuel cfg env [] body afterCondition = .stop stop after) :
    execWhile (fuel + 1) cfg env condition body state = .stop stop after := by
  simp only [execWhile, bind_apply, conditionDone, expectBool, pure_apply, ite_true, stopped]

theorem while_condition_false {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {fuel : Nat} {state after : St}
    (conditionDone : evalExpr fuel cfg env condition state = .ok (.bool false) after) :
    execWhile (fuel + 1) cfg env condition body state = .ok (.normal .unit) after := by
  simp only [execWhile, bind_apply, conditionDone, expectBool, pure_apply, Bool.false_eq_true, ite_false]

#print axioms accepted_while_iterations
#print axioms StmtSource.whileConditionChildAt
#print axioms StmtSource.whileBodyChildAt
#print axioms StmtSource.whileAfterBodyCanonical
#print axioms while_iteration_reentry
#print axioms while_condition_stop
#print axioms while_body_stop
#print axioms while_condition_false
end Goose.Lower
