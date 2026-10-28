import Goose.Lower.DemandWhileIterationFuel

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem while_iterations_condition_stop {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {count : Nat} {state current after : St}
    (iterations : WhileIterations cfg env condition body count state current)
    {fuel : Nat} {stop : Stop} (stopped : evalExpr fuel cfg env condition current = .stop stop after)
    (nonTimeout : stop ≠ .timeout) :
    ∃ total, execStmt total cfg env (.while condition body origin) state = .stop stop after := by
  have done : execWhile (fuel + 1) cfg env condition body current = .stop stop after :=
    while_condition_stop stopped
  apply while_iterations_stmt_replay iterations done
  intro final same
  exact nonTimeout (Res.stop.inj same).1

theorem while_iterations_body_stop {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {count : Nat} {state current middle after : St}
    (iterations : WhileIterations cfg env condition body count state current)
    {conditionFuel bodyFuel : Nat} {stop : Stop}
    (evaluated : evalExpr conditionFuel cfg env condition current = .ok (.bool true) middle)
    (stopped : execBlock bodyFuel cfg env [] body middle = .stop stop after) (nonTimeout : stop ≠ .timeout) :
    ∃ total, execStmt total cfg env (.while condition body origin) state = .stop stop after := by
  let larger := max conditionFuel bodyFuel
  have conditionLarge : evalExpr larger cfg env condition current = .ok (.bool true) middle :=
    ((Goose.Proofs.Fuel.monoAll conditionFuel larger (by dsimp [larger]; omega)).expr cfg env condition current).1 _ _ evaluated
  have bodyLarge : execBlock larger cfg env [] body middle = .stop stop after := by
    have agrees := (Goose.Proofs.Fuel.monoAll bodyFuel larger (by dsimp [larger]; omega)).block cfg env [] body middle
    rcases agrees.2 stop after stopped with timeout | done
    · cases stop <;> simp [Goose.Proofs.Fuel.isTimeout] at timeout
      exact (nonTimeout rfl).elim
    · exact done
  have done : execWhile (larger + 1) cfg env condition body current = .stop stop after :=
    while_body_stop conditionLarge bodyLarge
  apply while_iterations_stmt_replay iterations done
  intro final same
  exact nonTimeout (Res.stop.inj same).1

theorem while_iterations_condition_false {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {count : Nat} {state current after : St}
    (iterations : WhileIterations cfg env condition body count state current)
    {fuel : Nat} (evaluated : evalExpr fuel cfg env condition current = .ok (.bool false) after) :
    ∃ total, execStmt total cfg env (.while condition body origin) state = .ok (.normal .unit) after := by
  have done : execWhile (fuel + 1) cfg env condition body current = .ok (.normal .unit) after :=
    while_condition_false evaluated
  exact while_iterations_stmt_replay iterations done (by intro final same; cases same)

#print axioms while_iterations_condition_stop
#print axioms while_iterations_body_stop
#print axioms while_iterations_condition_false
end Goose.Lower
