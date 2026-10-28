import Goose.Lower.DemandWhileSource
import Goose.Proofs.Fuel

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem while_iterations_replay {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {count : Nat} {state after : St} (iterations : WhileIterations cfg env condition body count state after)
    {fuel : Nat} {result : Res Flow} (completed : execWhile fuel cfg env condition body after = result)
    (nonTimeout : ∀ final, result ≠ .stop .timeout final) :
    ∃ total, execWhile total cfg env condition body state = result := by
  induction iterations with
  | zero => exact ⟨fuel, completed⟩
  | @next count state afterCondition afterBody after conditionFuel bodyFuel flow conditionDone bodyDone reentry rest ih =>
    obtain ⟨tailFuel, tailDone⟩ := ih completed
    let larger := max (max conditionFuel bodyFuel) tailFuel
    have conditionLarge : evalExpr larger cfg env condition state = .ok (.bool true) afterCondition :=
      ((Goose.Proofs.Fuel.monoAll conditionFuel larger (by dsimp [larger]; omega)).expr cfg env condition state).1 _ _ conditionDone
    have bodyLarge : execBlock larger cfg env [] body afterCondition = .ok flow afterBody :=
      ((Goose.Proofs.Fuel.monoAll bodyFuel larger (by dsimp [larger]; omega)).block cfg env [] body afterCondition).1 _ _ bodyDone
    have tailLarge : execWhile larger cfg env condition body afterBody = result := by
      have agrees := (Goose.Proofs.Fuel.monoAll tailFuel larger (by dsimp [larger]; omega)).while_ cfg env condition body afterBody
      cases result with
      | ok value final => exact agrees.1 value final tailDone
      | stop reason final =>
        rcases agrees.2 reason final tailDone with timeout | done
        · cases reason <;> simp [Goose.Proofs.Fuel.isTimeout] at timeout
          exact (nonTimeout final rfl).elim
        · exact done
    exact ⟨larger + 1, (while_iteration_reentry conditionLarge bodyLarge reentry).trans tailLarge⟩

theorem while_iterations_stmt_replay {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {count : Nat} {state after : St}
    (iterations : WhileIterations cfg env condition body count state after)
    {fuel : Nat} {result : Res Flow} (completed : execWhile fuel cfg env condition body after = result)
    (nonTimeout : ∀ final, result ≠ .stop .timeout final) :
    ∃ total, execStmt total cfg env (.while condition body origin) state = result := by
  obtain ⟨fuel, done⟩ := while_iterations_replay iterations completed nonTimeout
  exact ⟨fuel + 1, by simpa only [execStmt] using done⟩

#print axioms while_iterations_replay
#print axioms while_iterations_stmt_replay
end Goose.Lower
